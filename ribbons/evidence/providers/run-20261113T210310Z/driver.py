#!/usr/bin/env python3
"""Replay frozen OAI providers, one exact module per leanchecker process.

No build, clean, cache operation or provider-source mutation is performed.
This checks providers relative to their imported Lean/mathlib environments.
It is not an independent kernel implementation or a replay of all mathlib.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import threading
import time


ROOT = Path(__file__).resolve().parents[1]


def utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    os.replace(temporary, path)


def stat_key(path: Path) -> list[int]:
    s = path.stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def checked_output(command: list[str], cwd: Path = ROOT) -> str:
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--workers", type=int, choices=(1, 2, 4), default=1)
    args = parser.parse_args()
    default_name = dt.datetime.now(dt.timezone.utc).strftime("run-%Y%m%dT%H%M%SZ")
    output = (args.output or ROOT / "evidence/providers" / default_name).resolve()
    output.mkdir(parents=True, exist_ok=False)
    logs = output / "logs"
    logs.mkdir()
    started = time.monotonic()
    record: dict = {
        "ok": False,
        "status": "initializing",
        "started_at": utc(),
        "cwd": str(ROOT),
        "output": str(output),
        "concurrency": args.workers,
        "process_policy": "one fresh process per exact module; no aggregate prefix",
        "scope": "provider kernel replay relative to imported Lean/mathlib environments",
        "limitations": [
            "This is the bundled Lean kernel checker, not an independent kernel implementation.",
            "Imported mathlib declarations are trusted as imported; mathlib is not freshly replayed.",
            "Provider axiom audit is a separate root-owned command and is not run by this script.",
            "No full landmark 2 or Theorem 1.8 completion follows from this record.",
        ],
        "axiom_audit_performed": False,
        "commands": [],
    }
    state_path = output / "verification.json"
    files: dict[str, dict] = {}
    processes: dict[int, subprocess.Popen] = {}
    command_records: dict[int, dict] = {}
    process_lock = threading.Lock()
    stop = threading.Event()
    executor: concurrent.futures.ThreadPoolExecutor | None = None
    peak_processes = 0

    def snapshot_commands() -> None:
        with process_lock:
            record["commands"] = [command_records[i] for i in sorted(command_records)]
            record["max_concurrent_processes_observed"] = peak_processes
        record["completed_module_count"] = len(record["commands"])

    def stop_processes() -> None:
        stop.set()
        with process_lock:
            active = list(processes.values())
        for process in active:
            try:
                os.killpg(process.pid, 15)
            except ProcessLookupError:
                pass
        for process in active:
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, 9)
                except ProcessLookupError:
                    pass
                process.wait()

    def bind(path: Path, role: str, expected: str | None = None) -> None:
        path = path.absolute()
        actual = digest(path)
        if expected is not None and actual != expected:
            raise RuntimeError(f"Source hash mismatch for {path}: {actual} != {expected}")
        item = {"path": str(path), "resolved_path": str(path.resolve()),
                "role": role, "sha256": actual, "stat": stat_key(path)}
        if str(path) in files and files[str(path)]["sha256"] != actual:
            raise RuntimeError(f"Input changed while being bound: {path}")
        files[str(path)] = item

    def unchanged(full_hash: bool = False) -> None:
        for item in files.values():
            p = Path(item["path"])
            if str(p.resolve()) != item["resolved_path"] or stat_key(p) != item["stat"]:
                raise RuntimeError(f"Frozen input changed during replay: {p}")
            if full_hash and digest(p) != item["sha256"]:
                raise RuntimeError(f"Frozen input hash changed during replay: {p}")

    try:
        provenance_path = ROOT / "vendor/provenance.json"
        provenance = json.loads(provenance_path.read_text())
        modules = provenance["modules"]
        declared = [m["module"] for m in modules]
        order = provenance["topological_order"]
        if provenance["module_count"] != 359 or len(declared) != 359:
            raise RuntimeError("Expected exactly the authorized 359 provider modules")
        if len(set(declared)) != 359 or len(order) != 359 or set(order) != set(declared):
            raise RuntimeError("Module inventory/topological-order mismatch")
        if any(n.startswith(m + ".") for m in declared for n in declared if n != m):
            raise RuntimeError("A requested module is also an aggregate prefix of another provider")
        source_by_module = {m["module"]: m for m in modules}
        record["modules"] = order
        record["expected_module_count"] = len(order)
        bind(Path(__file__), "verification script")
        bind(provenance_path, "provider provenance")
        bind(ROOT / "vendor/LICENSE.openai-math", "upstream license")
        for name in ("README.md", "ENDPOINTS.md"):
            bind(ROOT / "vendor" / name, "provider source notes")
        for patch in sorted((ROOT / "vendor/compatibility-patches").rglob("*.patch")):
            bind(patch, "compatibility patch")
        for directory, role in ((ROOT, "ribbons configuration"),
                                (ROOT.parent, "parent configuration baseline")):
            for name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json"):
                bind(directory / name, role)
        artifact_count = 0
        for module in order:
            m = source_by_module[module]
            expected_path = "/".join(module.split(".")) + ".lean"
            if m["path"] != expected_path:
                raise RuntimeError(f"Module/path mismatch: {module}")
            bind(ROOT / "vendor" / m["path"], "active provider source", m["active_sha256"])
            bind(ROOT / "vendor/upstream-original" / m["path"],
                 "original upstream source", m["upstream_sha256"])
            stem = ROOT / ".lake/build/lib/lean" / Path(*module.split("."))
            candidates = sorted(stem.parent.glob(stem.name + ".olean*"))
            candidates = [p for p in candidates if p.is_file() and not p.name.endswith(".hash")]
            if not stem.with_suffix(".olean").is_file():
                raise RuntimeError(f"Provider compiled artifact missing: {module}")
            for artifact in candidates:
                bind(artifact, "frozen provider compiled artifact")
                artifact_count += 1
        mathlib = ROOT / ".lake/packages/mathlib"
        revision = checked_output(["git", "rev-parse", "HEAD"], mathlib)
        expected_revision = provenance["pilot_target_mathlib"]
        if revision != expected_revision:
            raise RuntimeError(f"Unexpected actual mathlib revision {revision}")
        mathlib_status = checked_output(["git", "status", "--porcelain", "--untracked-files=no"], mathlib)
        if mathlib_status:
            raise RuntimeError("Pinned mathlib has tracked modifications: " + mathlib_status)
        record["actual_mathlib_revision"] = revision
        record["mathlib_tracked_status"] = mathlib_status
        for name in ("lean-toolchain", "lake-manifest.json"):
            bind(mathlib / name, "pinned mathlib metadata")
        bind(mathlib / ".lake/build/lib/lean/Mathlib.olean", "imported mathlib root artifact")
        for binary in ("lean", "leanchecker", "lake"):
            path = Path(checked_output(["lake", "env", "which", binary]))
            bind(path, "toolchain executable")
        record["lean_version"] = checked_output(["lake", "env", "lean", "--version"])
        record["lake_version"] = checked_output(["lake", "--version"])
        record["provider_compiled_artifact_count"] = artifact_count
        record["input_count"] = len(files)
        record["source_inputs_file"] = "inputs.json"
        write_json(output / "inputs.json", {"bound_at": utc(), "files": list(files.values())})
        record["source_inputs_sha256"] = digest(output / "inputs.json")
        unchanged(full_hash=True)
        record["status"] = "running"
        write_json(state_path, record)
        print(f"Started provider replay: {len(order)} modules; {args.workers} workers; {output}", flush=True)
        last_progress = time.monotonic()

        def replay_one(index: int, module: str) -> None:
            nonlocal peak_processes
            if stop.is_set():
                return
            unchanged()
            command = ["lake", "env", "leanchecker", "--verbose", module]
            log_name = f"{index:03d}-{module}.log"
            log_path = logs / log_name
            module_start = time.monotonic()
            module_started = utc()
            with log_path.open("wb") as stream:
                with process_lock:
                    if stop.is_set():
                        return
                    process = subprocess.Popen(command, cwd=ROOT, stdout=stream,
                                               stderr=subprocess.STDOUT, start_new_session=True)
                    processes[index] = process
                    peak_processes = max(peak_processes, len(processes))
                returncode = process.wait()
            elapsed = time.monotonic() - module_start
            m = source_by_module[module]
            result = {
                "index": index, "module": module, "command": command,
                "cwd": str(ROOT), "pid": process.pid, "started_at": module_started,
                "ended_at": utc(), "exit_code": returncode,
                "duration_seconds": elapsed, "raw_log": "logs/" + log_name,
                "raw_log_sha256": digest(log_path),
                "active_source_sha256": m["active_sha256"],
                "upstream_original_sha256": m["upstream_sha256"],
                "all_input_hashes_ref": record["source_inputs_sha256"],
            }
            with process_lock:
                command_records[index] = result
                processes.pop(index, None)
            unchanged()
            if returncode != 0:
                stop.set()
                raise RuntimeError(f"Kernel checker failed for {module}: exit {returncode}; {log_path}")

        executor = concurrent.futures.ThreadPoolExecutor(max_workers=args.workers)
        pending = {executor.submit(replay_one, i, module)
                   for i, module in enumerate(order, 1)}
        while pending:
            done, pending = concurrent.futures.wait(
                pending, timeout=10, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                future.result()
            unchanged()
            snapshot_commands()
            record["duration_seconds"] = time.monotonic() - started
            write_json(state_path, record)
            if time.monotonic() - last_progress >= 60 or not pending:
                print(f"Replayed {len(record['commands'])}/{len(order)}; "
                      f"active workers {len(processes)}; peak {peak_processes}", flush=True)
                last_progress = time.monotonic()
        executor.shutdown(wait=True)
        executor = None
        unchanged(full_hash=True)
        final_revision = checked_output(["git", "rev-parse", "HEAD"], mathlib)
        if final_revision != revision:
            raise RuntimeError("Actual mathlib revision changed during replay")
        record["final_mathlib_revision"] = final_revision
        record["inputs_unchanged"] = True
        record["ok"] = len(record["commands"]) == 359 and all(
            c["exit_code"] == 0 for c in record["commands"])
        record["status"] = "passed" if record["ok"] else "failed"
    except BaseException as error:
        stop_processes()
        if executor is not None:
            executor.shutdown(wait=True, cancel_futures=True)
        snapshot_commands()
        record["ok"] = False
        record["status"] = "failed"
        record["error"] = f"{type(error).__name__}: {error}"
        print(record["error"], file=sys.stderr, flush=True)
    record["ended_at"] = utc()
    record["duration_seconds"] = time.monotonic() - started
    write_json(state_path, record)
    print(json.dumps({"ok": record["ok"], "status": record["status"],
                      "completed": len(record["commands"]), "output": str(output),
                      "duration_seconds": record["duration_seconds"]}), flush=True)
    return 0 if record["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
