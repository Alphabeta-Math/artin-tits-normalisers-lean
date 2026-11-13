#!/usr/bin/env python3
"""Build, audit and exactly replay the frozen 23 landmark-2 project modules.

Provider and parent full verification/semantic review are separate. This script
binds their actual source inputs and imported artifacts; it replays only the
23 new project leaves and their import-only aggregate, one exact module per
fresh process. It never invokes cache/update/clean operations.
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
BASE = ROOT.parent
EXPECTED_LEAVES = (
    "AtomicCoxeter", "CofinalRibbons", "CoxeterProjection", "DeltaDivisibility",
    "FractionNormalForms", "Fundamental", "Landmark2", "NormalizerSplitting",
    "ParabolicReduction", "Positive", "PositiveEmbedding", "PositiveReindex",
    "PositiveRibbons", "PositiveSupport", "Presentation", "ReducedRibbons",
    "RibbonGroupoid", "RibbonLcm", "RibbonPositiveCalculus", "RibbonRelations",
    "RibbonUniversal", "RibbonWords", "SphericalPositive",
)
MODULES = ["ArtinRibbons." + leaf for leaf in EXPECTED_LEAVES] + ["ArtinRibbons"]
ALLOWLIST = {"propext", "Classical.choice", "Quot.sound"}

# The exact-module replay body follows the pinned Lean 4.36.0-rc2
# LeanChecker.replayFromImports. Unlike leanchecker's CLI prefix search it
# calls findOLean once for precisely the requested module. Private and server
# parts are loaded exactly as in that bundled checker.
EXACT_REPLAY = r'''import Lean.CoreM
import Lean.Replay

open Lean

unsafe def replayExact (module : Name) : IO Nat := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"Missing exact module artifact: {mFile}"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then
    throw <| IO.userError "Empty exact module data"
  else
    let (mod, _) := parts[0]
    let (_, state) ← importModulesCore mod.imports |>.run
    let env ← finalizeImport state mod.imports {} 0 false false (isModule := true)
    let mut newConstants := {}
    for name in parts[parts.size - 1].1.constNames, ci in parts[parts.size - 1].1.constants do
      newConstants := newConstants.insert name ci
    discard <| env.toKernelEnv.replay newConstants
    env.freeRegions
    return newConstants.size

unsafe def main (args : List String) : IO UInt32 := do
  try
    let [arg] := args | throw <| IO.userError "Expected one exact module name"
    initSearchPath (← findSysroot)
    let count ← replayExact arg.toName
    let row := Json.mkObj [("module", toJson arg), ("declarations", toJson count),
      ("exact", toJson true), ("kernel_replay_passed", toJson true)]
    IO.println s!"EXACT_REPLAY_JSON {row.compress}"
    return 0
  catch error =>
    IO.eprintln s!"Exact kernel replay failed: {error}"
    return 1
'''


def utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def map_digest(value: dict) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def stat_key(path: Path) -> list[int]:
    s = path.stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def write_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    os.replace(temporary, path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--workers", type=int, choices=(1, 2), default=2)
    args = parser.parse_args()
    stamp = dt.datetime.now(dt.timezone.utc).strftime("run-%Y%m%dT%H%M%SZ")
    output = (args.output or ROOT / "evidence/project" / stamp).resolve()
    output.mkdir(parents=True, exist_ok=False)
    (output / "logs").mkdir()
    started = time.monotonic()
    env = dict(os.environ)
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    env.setdefault("LEAN_NUM_THREADS", "2")
    record = {
        "kind": "theorem18-landmark2-project-recheck", "ok": False,
        "status": "initializing", "started_at": utc(), "cwd": str(ROOT),
        "scope": "All 23 actual ArtinRibbons scientific modules and their aggregate",
        "full_theorem_1_8_proved": False, "provider_kernel_replay_performed": False,
        "semantic_statement_review_performed": False,
        "limitations": [
            "Uses the bundled Lean kernel relative to imported environments, not an independent kernel.",
            "Does not freshly replay mathlib, parent or provider declarations; those have separate verification.",
            "The import-only aggregate legitimately has zero declarations; all 23 scientific leaves must be nonempty.",
        ],
        "replay_workers": args.workers, "expected_modules": MODULES,
        "expected_scientific_module_count": 23, "expected_exact_replay_count": 24,
        "commands": [],
    }
    files: dict[str, dict] = {}
    lock = threading.Lock()

    def save() -> None:
        record["duration_seconds"] = round(time.monotonic() - started, 3)
        write_json(output / "verification.json", record)

    def bind(path: Path, role: str, expected: str | None = None) -> None:
        p = path.absolute()
        actual = digest(p)
        if expected is not None and actual != expected:
            raise RuntimeError(f"Source/input mismatch: {p}: {actual} != {expected}")
        item = {"path": str(p), "resolved_path": str(p.resolve()), "role": role,
                "sha256": actual, "stat": stat_key(p)}
        if str(p) in files and files[str(p)]["sha256"] != actual:
            raise RuntimeError("Input changed while being bound: " + str(p))
        files[str(p)] = item

    def unchanged(full_hash: bool = False) -> None:
        for item in files.values():
            p = Path(item["path"])
            if str(p.resolve()) != item["resolved_path"] or stat_key(p) != item["stat"]:
                raise RuntimeError("Frozen input changed during verification: " + str(p))
            if full_hash and digest(p) != item["sha256"]:
                raise RuntimeError("Frozen input hash changed during verification: " + str(p))

    def run(label: str, argv: list[str], *, module: str | None = None,
            check: bool = True) -> dict:
        log = output / "logs" / (label + ".log")
        began = time.monotonic()
        item = {"label": label, "argv": argv, "cwd": str(ROOT), "started_at": utc()}
        if module is not None:
            item["module"] = module
        print("Running:", label, flush=True)
        with log.open("wb") as stream:
            result = subprocess.run(argv, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
        item.update({"exit_code": result.returncode, "finished_at": utc(),
                     "duration_seconds": round(time.monotonic() - began, 3),
                     "log": str(log.relative_to(output)), "log_sha256": digest(log)})
        with lock:
            record["commands"].append(item)
            save()
        if check and result.returncode:
            raise RuntimeError(f"{label} failed with exit {result.returncode}; {log}")
        return item

    def read_log(item: dict) -> str:
        return (output / item["log"]).read_text()

    def rows(item: dict, prefix: str) -> list[dict]:
        return [json.loads(line[len(prefix):]) for line in read_log(item).splitlines()
                if line.startswith(prefix)]

    try:
        inventory_path = ROOT / "source-inventory.json"
        inventory = json.loads(inventory_path.read_text())
        actual_project = {"ribbons/ArtinRibbons.lean": digest(ROOT / "ArtinRibbons.lean")}
        actual_project.update({"ribbons/" + str(p.relative_to(ROOT)): digest(p)
                               for p in sorted((ROOT / "ArtinRibbons").rglob("*.lean"))})
        expected_paths = {"ribbons/" + m.replace(".", "/") + ".lean" for m in MODULES}
        if set(actual_project) != expected_paths or len(actual_project) != 24:
            raise RuntimeError("Missing, extra or unexpected project source modules")
        if actual_project != inventory["project_source_sha256"]:
            raise RuntimeError("Frozen project source inventory mismatch")
        if inventory["full_theorem_1_8_proved"] is not False:
            raise RuntimeError("Incorrect full Theorem 1.8 scope assertion")
        audit_imports = {line.split()[-1] for line in (ROOT / "ProjectAudit.lean").read_text().splitlines()
                         if line.startswith("import ArtinRibbons")}
        if audit_imports != set(MODULES):
            raise RuntimeError("Project audit does not explicitly import every exact project module")
        bind(Path(__file__), "project verifier")
        bind(ROOT / "ProjectAudit.lean", "defining-module axiom audit")
        bind(inventory_path, "frozen source and actual declaration inventory")
        for key in ("project_source_sha256", "configuration_sha256", "provider_active_source_sha256",
                    "provider_original_source_sha256", "provider_compatibility_patch_sha256"):
            for name, expected in inventory[key].items():
                bind(BASE / name, key, expected)
        provenance_path = ROOT / "vendor/provenance.json"
        bind(provenance_path, "provider provenance", inventory["vendor_provenance_sha256"])
        provenance = json.loads(provenance_path.read_text())
        for kind in ("active", "original"):
            if map_digest(inventory[f"provider_{kind}_source_sha256"]) != inventory[f"provider_{kind}_aggregate_sha256"]:
                raise RuntimeError("Provider source aggregate mismatch: " + kind)
        parent_record_path = BASE / inventory["parent_verification_path"]
        bind(parent_record_path, "accepted parent verification", inventory["parent_verification_sha256"])
        parent = json.loads(parent_record_path.read_text())
        if parent["ok"] is not True or map_digest(parent["input_sha256"]) != inventory["parent_input_aggregate_sha256"]:
            raise RuntimeError("Accepted parent evidence/input map mismatch")
        for name, expected in parent["input_sha256"].items():
            bind(BASE / name, "parent verified context", expected)
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
            bind(BASE / name, "parent dependency configuration")
        record["repository_head"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        record["project_source_sha256"] = actual_project
        record["source_inventory_sha256"] = digest(inventory_path)
        record["provider_provenance_sha256"] = digest(provenance_path)
        record["parent_verification_sha256"] = digest(parent_record_path)
        save()
        run("lean-version", ["lake", "env", "lean", "--version"])
        run("lake-version", ["lake", "--version"])
        rev = run("mathlib-revision", ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"])
        if read_log(rev).strip() != provenance["pilot_target_mathlib"]:
            raise RuntimeError("Actual mathlib revision does not match the pin")
        record["actual_mathlib_revision"] = read_log(rev).strip()
        status = run("mathlib-tracked-status", ["git", "-C", ".lake/packages/mathlib", "status",
                                                "--porcelain", "--untracked-files=no"])
        if read_log(status).strip():
            raise RuntimeError("Pinned mathlib has tracked modifications")
        run("build-project", ["lake", "build", "ArtinRibbons"])
        unchanged(full_hash=True)
        audit = run("project-axioms-and-statements", ["lake", "env", "lean", "ProjectAudit.lean"])
        declarations = rows(audit, "PROJECT_DECL_JSON ")
        module_rows = rows(audit, "PROJECT_MODULE_JSON ")
        compiled_rows = rows(audit, "PROJECT_COMPILED_MODULE_JSON ")
        duplicate_rows = rows(audit, "PROJECT_DUPLICATE_JSON ")
        by_module = {m: [] for m in MODULES}
        for row in declarations:
            if row["module"] not in by_module or not set(row["axioms"]) <= ALLOWLIST:
                raise RuntimeError("Unexpected audit module or forbidden transitive axiom")
            by_module[row["module"]].append(row["name"])
        if not declarations or len({r["name"] for r in declarations}) != len(declarations):
            raise RuntimeError("Empty or duplicate declaration audit")
        by_module = {m: sorted(names) for m, names in sorted(by_module.items())}
        if any(not by_module[m] for m in MODULES if m != "ArtinRibbons"):
            raise RuntimeError("Empty scientific module audit")
        if by_module != inventory["audited_declarations_by_module"]:
            raise RuntimeError("Actual Lean declaration inventory changed or is incomplete")
        if len(module_rows) != 24 or {r["module"] for r in module_rows} != set(MODULES):
            raise RuntimeError("Missing/duplicate module audit coverage")
        for row in module_rows:
            if row["imported"] is not True or row["declarations"] != len(by_module[row["module"]]):
                raise RuntimeError("Module/declaration audit counts disagree")
        if len(compiled_rows) != 24 or {r["module"] for r in compiled_rows} != set(MODULES):
            raise RuntimeError("Missing/duplicate physical compiled-module coverage")
        compiled_by_module = {r["module"]: sorted(r["names"]) for r in compiled_rows}
        for row in compiled_rows:
            if row["declarations"] != len(row["names"]) or len(set(row["names"])) != len(row["names"]):
                raise RuntimeError("Malformed physical compiled declaration inventory")
        if compiled_by_module != inventory["compiled_declaration_occurrences_by_module"]:
            raise RuntimeError("Actual compiled declaration occurrence inventory changed")
        duplicate_key = lambda r: (r["physical_module"], r["name"])
        if sorted(duplicate_rows, key=duplicate_key) != sorted(
                inventory["compiled_duplicate_equivalences"], key=duplicate_key):
            raise RuntimeError("Actual duplicate-declaration equivalence evidence changed")
        aliases = {}
        for row in duplicate_rows:
            if not all(row[k] is True for k in
                       ("same_type", "same_proof", "same_universe_parameters", "theorem_in_both")):
                raise RuntimeError("Compiled declaration overlap has no exact theorem-content match")
            key = duplicate_key(row)
            if key in aliases or row["name"] not in by_module[row["canonical_module"]]:
                raise RuntimeError("Duplicate declaration has no unique audited canonical owner")
            aliases[key] = row["canonical_module"]
        semantic_names = {name for names in by_module.values() for name in names}
        if {name for names in compiled_by_module.values() for name in names} != semantic_names:
            raise RuntimeError("Physical declarations and audited semantic declarations disagree")
        for module, names in compiled_by_module.items():
            for name in names:
                if name not in by_module[module] and (module, name) not in aliases:
                    raise RuntimeError("Physical declaration occurrence lacks an audited owner/equality certificate")
        if sum(map(len, compiled_by_module.values())) != len(declarations) + len(aliases):
            raise RuntimeError("Physical/semantic declaration counts disagree")
        record["audited_modules"] = sorted(by_module)
        record["audited_declaration_count"] = len(declarations)
        record["compiled_declaration_occurrence_count"] = sum(map(len, compiled_by_module.values()))
        record["compiled_duplicate_equivalences"] = duplicate_rows
        write_json(output / "audited-declarations.json", by_module)
        record["audited_declarations_sha256"] = digest(output / "audited-declarations.json")
        write_json(output / "compiled-declaration-occurrences.json", compiled_by_module)
        record["compiled_declaration_occurrences_sha256"] = digest(output / "compiled-declaration-occurrences.json")

        # Bind the compiled project and direct imported interfaces after the build.
        # --deps is recorded for each exact source, independently of replay.
        compiled: set[Path] = set()
        for i, module in enumerate(MODULES):
            source = ROOT / (module.replace(".", "/") + ".lean")
            dependency_log = run(f"deps-{i:02d}-{module}", ["lake", "env", "lean", "--deps", str(source)],
                                 module=module)
            for line in read_log(dependency_log).splitlines():
                if line.endswith(".olean"):
                    compiled.add(Path(line).absolute())
            compiled.add(ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean"))
        for item in provenance["modules"]:
            compiled.add(ROOT / ".lake/build/lib/lean" / (item["module"].replace(".", "/") + ".olean"))
        for path in sorted(compiled):
            bind(path, "imported/project compiled interface")
            for ending in (".server", ".private"):
                candidate = Path(str(path) + ending)
                if candidate.exists():
                    bind(candidate, "imported/project compiled auxiliary part")
        runner = output / "ExactReplay.lean"
        runner.write_text(EXACT_REPLAY)
        bind(runner, "exact replay runner, copied from pinned checker algorithm")
        checker_source = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
                             cwd=ROOT, env=env, text=True).strip()) / "src/lean/LeanChecker.lean"
        if checker_source.exists():
            bind(checker_source, "pinned checker reference source")
        for tool in ("lean", "lake"):
            tool_path = Path(subprocess.check_output(["lake", "env", "which", tool], cwd=ROOT,
                              env=env, text=True).strip())
            bind(tool_path, "toolchain executable")
        write_json(output / "inputs.json", {"bound_at": utc(), "files": list(files.values())})
        record["inputs_sha256"] = digest(output / "inputs.json")
        record["bound_input_count"] = len(files)
        record["compiled_interface_count"] = len(compiled)
        record["status"] = "replaying"
        save()
        unchanged(full_hash=True)
        results = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures = {pool.submit(run, f"replay-{i:02d}-{module}",
                                   ["lake", "env", "lean", "--run", str(runner), module],
                                   module=module, check=False): module
                       for i, module in enumerate(MODULES)}
            for future in concurrent.futures.as_completed(futures):
                item = future.result()
                module = futures[future]
                replay_rows = rows(item, "EXACT_REPLAY_JSON ")
                expected_count = len(compiled_by_module[module])
                valid = (item["exit_code"] == 0 and len(replay_rows) == 1
                         and replay_rows[0]["module"] == module
                         and replay_rows[0]["exact"] is True
                         and replay_rows[0]["kernel_replay_passed"] is True
                         and replay_rows[0]["declarations"] == expected_count)
                results.append({"module": module, "ok": valid,
                                "declarations_expected": expected_count, "runner_output": replay_rows})
                record["exact_replays"] = sorted(results, key=lambda r: r["module"])
                save()
                unchanged()
        if len(results) != 24 or not all(r["ok"] for r in results):
            raise RuntimeError("One or more exact module replays failed or had incomplete declaration coverage")
        unchanged(full_hash=True)
        record["inputs_unchanged"] = True
        record["ok"] = True
        record["status"] = "passed"
    except BaseException as error:
        record["status"] = "failed"
        record["error"] = f"{type(error).__name__}: {error}"
        print(record["error"], file=sys.stderr, flush=True)
    finally:
        record["finished_at"] = utc()
        save()
    print(json.dumps({"ok": record["ok"], "status": record["status"],
                      "output": str(output), "commands": len(record["commands"]),
                      "duration_seconds": record["duration_seconds"]}), flush=True)
    return 0 if record["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
