#!/usr/bin/env python3
"""Verify Theorem 1.8 foundations; never certify the unproved full theorem."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs/theorem18"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", default="evidence/theorem18-local")
args = parser.parse_args()
out = Path(args.output)
if not out.is_absolute():
    out = ROOT / out
out.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
env.setdefault("LEAN_NUM_THREADS", "2")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def project_sources():
    files = [ROOT / "ArtinTheorem18.lean",
             *sorted(ROOT.glob("ArtinNormalisers/Theorem18/**/*.lean"))]
    return {str(p.relative_to(ROOT)): digest(p) for p in files}


def inputs():
    files = [*ROOT.glob("*.lean"), *ROOT.glob("ArtinNormalisers/**/*.lean"),
             *ROOT.glob("vendor/**/*.lean"), *ROOT.glob("scripts/*.py"),
             *ROOT.glob("vendor/*provenance.json")]
    files += [ROOT / name for name in [
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", "README.md",
        "vendor/LICENSE.TauCeti", "vendor/README.md",
        "docs/theorem18/source-inventory.json",
        "docs/full/source-inventory.json",
    ]]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(set(files))}


def git(*argv):
    return subprocess.check_output(["git", *argv], cwd=ROOT, text=True).strip()


record = {
    "kind": "theorem18-foundations-verification",
    "scope": "Actual geometric definitions/action/topology and generic covering/asphericity suppliers; NOT Theorem 1.8",
    "full_theorem_1_8_proved": False,
    "started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "repository_head": git("rev-parse", "HEAD"),
    "worktree_status": git("status", "--porcelain"),
    "input_sha256": {},
    "commands": [],
    "ok": False,
}


def save():
    (out / "verification.json").write_text(json.dumps(record, indent=2) + "\n")


def check_sources_and_reviews():
    inventory_path = DOCS / "source-inventory.json"
    inventory = json.loads(inventory_path.read_text())
    actual = project_sources()
    if inventory["project_source_sha256"] != actual:
        raise RuntimeError("Missing, extra or stale foundation source")
    configuration = {name: digest(ROOT / name) for name in
                     ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]}
    if inventory["configuration_sha256"] != configuration:
        raise RuntimeError("Changed reviewed toolchain/dependencies/elaboration options")
    if inventory["full_theorem_1_8_proved"] is not False:
        raise RuntimeError("Foundations must not assert full Theorem 1.8 completion")
    old_path = ROOT / "vendor/provenance.json"
    new_path = ROOT / "vendor/theorem18-provenance.json"
    old = json.loads(old_path.read_text())
    new = json.loads(new_path.read_text())
    if digest(new_path) != inventory["new_vendor_provenance_sha256"]:
        raise RuntimeError("Changed foundation supplier provenance")
    if digest(old_path) != new["historical_provenance_sha256"]:
        raise RuntimeError("Changed historical supplier provenance")
    if digest(ROOT / "docs/full/source-inventory.json") != inventory["historical_source_inventory_sha256"]:
        raise RuntimeError("Changed historical algebraic source inventory")
    if old["revision"] != new["revision"]:
        raise RuntimeError("Supplier revisions disagree")
    merged = {}
    for provider in [old, new]:
        modules = {m.replace(".", "/") + ".lean" for m in provider["modules"]}
        if modules != set(provider["files_sha256"]):
            raise RuntimeError("Supplier module/file inventories disagree")
        for relative, sha in provider["files_sha256"].items():
            if relative in merged or digest(ROOT / "vendor" / relative) != sha:
                raise RuntimeError("Duplicate or changed supplier: " + relative)
            merged[relative] = sha
    on_disk = {str(p.relative_to(ROOT / "vendor"))
               for p in ROOT.glob("vendor/TauCeti/**/*.lean")}
    if on_disk != set(merged):
        raise RuntimeError("Missing or extra supplier modules")
    if digest(ROOT / "vendor/LICENSE.TauCeti") != new["license"]["sha256"]:
        raise RuntimeError("Changed supplier license")
    record["independent_reviews"] = []
    for label in ["a", "b"]:
        path = DOCS / "reviews" / ("foundations-" + label + ".json")
        review = json.loads(path.read_text())
        if review["verdict"] != "accept-foundations-only":
            raise RuntimeError("Foundation review not accepted: " + label)
        if review["model"] != "gpt-6.1-sol" or review["reasoning_effort"] != "high":
            raise RuntimeError("Unexpected independent reviewer configuration")
        if review["full_theorem_1_8_proved"] is not False:
            raise RuntimeError("Reviewer claims an unproved theorem")
        if review["project_source_sha256"] != actual:
            raise RuntimeError("Incomplete or stale source review: " + label)
        if review["configuration_sha256"] != configuration:
            raise RuntimeError("Changed reviewed configuration: " + label)
        if review["provider_source_sha256"] != new["files_sha256"]:
            raise RuntimeError("Incomplete or stale provider review: " + label)
        if review["new_vendor_provenance_sha256"] != digest(new_path):
            raise RuntimeError("Changed reviewed supplier provenance")
        if review["historical_source_inventory_sha256"] != inventory["historical_source_inventory_sha256"]:
            raise RuntimeError("Changed reviewed historical algebraic inputs")
        record["independent_reviews"].append({
            "reviewer": label, "json_sha256": digest(path),
            "markdown_sha256": digest(path.with_suffix(".md")),
        })
    record["source_inventory_sha256"] = digest(inventory_path)
    record["new_vendor_provenance_sha256"] = digest(new_path)
    record["upstream_supplier_revision"] = new["revision"]
    return new


save()
try:
    provider = check_sources_and_reviews()
    record["input_sha256"] = inputs()
    project_modules = ["ArtinNormalisers.Theorem18." +
                       str(p.relative_to(ROOT / "ArtinNormalisers/Theorem18"))
                       .removesuffix(".lean").replace("/", ".")
                       for p in sorted(ROOT.glob("ArtinNormalisers/Theorem18/**/*.lean"))]
    commands = [
        ("lean-version", ["lean", "--version"]),
        ("lake-version", ["lake", "--version"]),
        ("mathlib-revision", ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]),
        ("build-foundations", ["lake", "build", "ArtinTheorem18"]),
        ("foundation-and-provider-axioms", ["lake", "env", "lean", "-DwarningAsError=true", "Theorem18Audit.lean"]),
        *[("replay-" + module.replace(".", "-"), [
            "lake", "env", "leanchecker", "--verbose", module,
        ]) for module in [*provider["modules"], *project_modules]],
    ]
    save()
    for label, cmd in commands:
        log = out / (label + ".log")
        print("Running:", " ".join(cmd), flush=True)
        start = time.monotonic()
        with log.open("w") as stream:
            result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT)
        record["commands"].append({
            "argv": cmd, "exit_code": result.returncode, "log": log.name,
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "log_sha256": digest(log),
        })
        save()
        if result.returncode:
            print(log.read_text(), flush=True)
            raise RuntimeError(label + " failed")
        if label == "foundation-and-provider-axioms":
            old = json.loads((ROOT / "vendor/provenance.json").read_text())
            expected_modules = set(old["modules"] + provider["modules"] + project_modules)
            seen_modules = {line.split()[1] for line in log.read_text().splitlines()
                            if line.startswith("FOUNDATION_AXIOMS ")}
            if seen_modules != expected_modules:
                raise RuntimeError("Axiom audit has incomplete or unexpected module coverage: " +
                                   str(sorted(seen_modules ^ expected_modules)))
            record["audited_modules"] = sorted(seen_modules)
    if inputs() != record["input_sha256"]:
        raise RuntimeError("Inputs changed during foundation verification")
    before = list(record["independent_reviews"])
    check_sources_and_reviews()
    if record["independent_reviews"] != before:
        raise RuntimeError("Review receipts changed during verification")
    revision = (out / "mathlib-revision.log").read_text().strip()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    expected = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    if revision != expected or revision != provider["project_mathlib_revision"]:
        raise RuntimeError("Mathlib checkout/manifest/provider pins disagree")
    record["ok"] = True
except Exception as exc:
    record["error"] = str(exc)
    raise
finally:
    record["finished_at"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save()
print("Foundations verified. Full Theorem 1.8 remains unproved.", flush=True)
