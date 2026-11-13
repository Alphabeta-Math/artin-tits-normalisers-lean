#!/usr/bin/env python3
"""Verify full algebraic Lemma 2.8 and its directly used third-party suppliers."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
REVIEWS = ROOT / "docs/full/reviews"
parser = argparse.ArgumentParser()
parser.add_argument("--output", default="evidence/full-local")
args = parser.parse_args()
out = Path(args.output)
if not out.is_absolute():
    out = ROOT / out
out.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
env.setdefault("LEAN_NUM_THREADS", "2")


def science_inputs():
    files = [ROOT / "ArtinNormalisers.lean", ROOT / "ArtinNormalisersFull.lean",
             *sorted(ROOT.glob("ArtinNormalisers/**/*.lean"))]
    return {str(f.relative_to(ROOT)): hashlib.sha256(f.read_bytes()).hexdigest()
            for f in files}


def inputs():
    files = [*ROOT.glob("*.lean"), *ROOT.glob("ArtinNormalisers/**/*.lean"),
             *ROOT.glob("vendor/**/*.lean"), *ROOT.glob("scripts/*.py")]
    files += [ROOT / name for name in [
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", "README.md",
        "vendor/provenance.json", "vendor/LICENSE.TauCeti", "vendor/README.md",
    ]]
    return {str(f.relative_to(ROOT)): hashlib.sha256(f.read_bytes()).hexdigest()
            for f in sorted(set(files))}


def git(*argv):
    return subprocess.check_output(["git", *argv], cwd=ROOT, text=True).strip()


record = {
    "kind": "lean-lemma28-full-algebraic-verification",
    "started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "repository_head": git("rev-parse", "HEAD"),
    "input_sha256": inputs(),
    "scope": "Full short exact sequence for standard presentation-defined Artin groups; topological/presentation equivalence not formalized",
    "commands": [],
    "ok": False,
}


def check_reviews():
    inventory_file = REVIEWS.parent / "source-inventory.json"
    inventory = json.loads(inventory_file.read_text())
    actual = science_inputs()
    if inventory["project_source_sha256"] != actual:
        raise RuntimeError("Stale project source inventory")
    expected_declarations = {row["name"] for row in inventory["declarations"]}
    provenance_path = ROOT / "vendor/provenance.json"
    provenance_digest = hashlib.sha256(provenance_path.read_bytes()).hexdigest()
    provenance = json.loads(provenance_path.read_text())
    if provenance_digest != inventory["vendor_provenance_sha256"]:
        raise RuntimeError("Vendor provenance changed after statement review")
    for relative, digest in provenance["files_sha256"].items():
        if hashlib.sha256((ROOT / "vendor" / relative).read_bytes()).hexdigest() != digest:
            raise RuntimeError("Changed upstream supplier source: " + relative)
    module_files = {m.replace(".", "/") + ".lean" for m in provenance["modules"]}
    if module_files != set(provenance["files_sha256"]):
        raise RuntimeError("Supplier module/file inventories disagree")
    actual_vendor = {str(p.relative_to(ROOT / "vendor"))
                     for p in ROOT.glob("vendor/TauCeti/**/*.lean")}
    if actual_vendor != module_files:
        raise RuntimeError("Missing or extra supplier modules")
    record["source_inventory_sha256"] = hashlib.sha256(inventory_file.read_bytes()).hexdigest()
    record["vendor_provenance_sha256"] = provenance_digest
    record["upstream_supplier_revision"] = provenance["revision"]
    record["independent_reviews"] = []
    for reviewer in ["reviewer-a", "reviewer-b"]:
        file = REVIEWS / (reviewer + ".json")
        review = json.loads(file.read_text())
        if review["verdict"] not in ["accept", "accepted"]:
            raise RuntimeError(f"{reviewer} did not accept")
        if review["model"] != "gpt-6.1-sol" or review["reasoning_effort"] != "high":
            raise RuntimeError(f"Unexpected reviewer configuration: {reviewer}")
        if review["source_sha256"] != actual:
            raise RuntimeError(f"Incomplete or stale reviewed source: {reviewer}")
        if set(review["declarations"]) != expected_declarations:
            raise RuntimeError(f"Incomplete declaration review: {reviewer}")
        if review["vendor_provenance_sha256"] != provenance_digest:
            raise RuntimeError(f"Stale vendor review: {reviewer}")
        if review["provider_source_sha256"] != provenance["files_sha256"]:
            raise RuntimeError(f"Incomplete provider source binding: {reviewer}")
        record["independent_reviews"].append({
            "reviewer": reviewer, "verdict": review["verdict"],
            "json_sha256": hashlib.sha256(file.read_bytes()).hexdigest(),
        })


def save():
    (out / "verification.json").write_text(json.dumps(record, indent=2) + "\n")


provenance = json.loads((ROOT / "vendor/provenance.json").read_text())
project_modules = ["ArtinNormalisers." + str(p.relative_to(ROOT / "ArtinNormalisers"))
                   .removesuffix(".lean").replace("/", ".")
                   for p in sorted(ROOT.glob("ArtinNormalisers/**/*.lean"))]
commands = [
    ("lean-version", ["lean", "--version"]),
    ("lake-version", ["lake", "--version"]),
    ("mathlib-revision", ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]),
    ("clean", ["lake", "clean", "artin-normalisers"]),
    ("build", ["lake", "build", "ArtinNormalisersFull"]),
    ("project-axioms", ["lake", "env", "lean", "-DwarningAsError=true", "FullAudit.lean"]),
    ("provider-axioms", ["lake", "env", "lean", "-DwarningAsError=true", "ProviderAudit.lean"]),
    # Single-module invocations avoid the bundled rc2 aggregate replay crash.
    *[("replay-" + module.replace(".", "-"), [
        "lake", "env", "leanchecker", "--verbose", module,
    ]) for module in [*provenance["modules"], *project_modules]],
]

save()
try:
    check_reviews()
    save()
    for label, cmd in commands:
        log = out / (label + ".log")
        start = time.monotonic()
        print("Running:", " ".join(cmd), flush=True)
        with log.open("w") as stream:
            result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT)
        record["commands"].append({
            "argv": cmd, "exit_code": result.returncode, "log": log.name,
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
        })
        save()
        if result.returncode:
            print(log.read_text(), flush=True)
            raise RuntimeError(f"{label} failed with exit code {result.returncode}")
    if inputs() != record["input_sha256"]:
        raise RuntimeError("Project inputs changed during verification")
    before_reviews = list(record["independent_reviews"])
    check_reviews()
    if record["independent_reviews"] != before_reviews:
        raise RuntimeError("Independent review receipts changed during verification")
    actual = (out / "mathlib-revision.log").read_text().strip()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    expected = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    if actual != expected or actual != provenance["project_mathlib_revision"]:
        raise RuntimeError("Mathlib checkout/manifest/vendor verification pins disagree")
    record["ok"] = True
except Exception as exc:
    record["error"] = str(exc)
    raise
finally:
    record["finished_at"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save()
print("Full Lemma 2.8: build, two independent review bindings, project/supplier axiom audits and sequential kernel replays passed.", flush=True)
