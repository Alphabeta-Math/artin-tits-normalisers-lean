#!/usr/bin/env python3
"""Record real checks for the selected twenty-one-module provider; never alter caches."""

import datetime
import hashlib
import json
import pathlib
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[2]
REPO = ROOT.parent
EVIDENCE = ROOT / "evidence/providers"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def snapshot(artifacts):
    paths = {p for p in (ROOT / "vendor").rglob("*") if p.is_file()}
    paths.update(p for p in (ROOT / "scripts/providers").glob("*.py") if p.is_file())
    paths.add(ROOT / "ProviderAudit.lean")
    paths.add(ROOT / "evidence/providers/source-inspection.json")
    provenance = json.loads((ROOT / "vendor/provenance.json").read_text())
    paths.update(REPO / row["repository_relative_source"] for row in provenance["reused_pinned_dependencies"])
    for base in [REPO, REPO / "landmarks", REPO / "ribbons", REPO / "chambers", REPO / "sequences", REPO / "asphericity", ROOT]:
        for name in ["lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json"]:
            path = base / name
            if path.is_file():
                paths.add(path)
    if artifacts:
        paths.update(p for p in (ROOT / ".lake/build/lib/lean/ArtinHomotopyVendor").rglob("*")
                     if p.is_file() and ".olean" in p.name)
    return {str(p.relative_to(REPO)): digest(p) for p in sorted(paths)}


def main():
    phase = sys.argv[1]
    assert phase in {"build", "audit", "replay"}
    provenance = json.loads((ROOT / "vendor/provenance.json").read_text())
    modules = provenance["topological_order"]
    run = EVIDENCE / (phase + "-" + datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ"))
    run.mkdir(parents=True)
    before = snapshot(phase != "build")
    (run / "inputs-before.json").write_text(json.dumps(before, indent=2) + "\n")
    record = {
        "ok": False, "phase": phase, "cwd": str(ROOT), "started_at": now(),
        "modules": modules, "commands": [],
        "scope": "Exact selected provider declarations; replay relative to pinned imported Mathlib (all non-Mathlib closure modules selected)",
        "build_mode": "explicit Lake provider target; no dependency update or cache cleanup",
        "independent_statement_reviews_pending": True,
        "root_mathematical_acceptance_pending": True,
        "full_landmark_5_proved": False, "full_theorem_1_8_proved": False,
    }
    commands = [["python3", "scripts/providers/assemble.py", "--check"]]
    commands += ([["lake", "build", *modules]] if phase == "build" else
                 [["lake", "env", "lean", "ProviderAudit.lean"]] if phase == "audit" else
                 [["lake", "env", "leanchecker", "--verbose", module] for module in modules])
    (run / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    for index, command in enumerate(commands):
        log = run / (f"{index:02d}-" + phase + ".log")
        start = time.monotonic()
        with log.open("wb") as stream:
            result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        row = {"command": command, "cwd": str(ROOT), "exit_code": result.returncode,
               "duration_seconds": time.monotonic() - start, "log": log.name,
               "log_sha256": digest(log)}
        record["commands"].append(row)
        (run / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
        print(json.dumps(row), flush=True)
        if result.returncode:
            break
    after = snapshot(phase != "build")
    (run / "inputs-after.json").write_text(json.dumps(after, indent=2) + "\n")
    record.update({"ended_at": now(), "inputs_unchanged": before == after,
                   "inputs_before_sha256": digest(run / "inputs-before.json"),
                   "inputs_after_sha256": digest(run / "inputs-after.json"),
                   "ok": len(record["commands"]) == len(commands)
                   and all(row["exit_code"] == 0 for row in record["commands"]) and before == after})
    (run / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(str(run), flush=True)
    sys.exit(0 if record["ok"] else 1)


if __name__ == "__main__":
    main()
