#!/usr/bin/env python3
"""Verify landmark 1 only: the actual finite-type normalizer quotient covering."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", default="landmarks/evidence/landmark1-local")
args = parser.parse_args()
out = Path(args.output)
if not out.is_absolute():
    out = BASE / out
out.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
env.setdefault("LEAN_NUM_THREADS", "2")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def project_sources():
    paths = [ROOT / "ArtinLandmarks.lean", *sorted(ROOT.glob("ArtinLandmarks/**/*.lean"))]
    return {str(p.relative_to(BASE)): sha(p) for p in paths}


def check_bindings():
    inv = json.loads((ROOT / "source-inventory.json").read_text())
    actual = project_sources()
    if inv["project_source_sha256"] != actual:
        raise RuntimeError("Missing, extra or changed landmark proof sources")
    config = {str(p.relative_to(BASE)): sha(p) for p in
              [ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json"]}
    if inv["configuration_sha256"] != config:
        raise RuntimeError("Changed landmark configuration")
    if inv["landmark_1_proved"] is not True or inv["full_theorem_1_8_proved"] is not False:
        raise RuntimeError("Incorrect scope assertion")
    provenance_path = ROOT / "vendor/provenance.json"
    provider = json.loads(provenance_path.read_text())
    if sha(provenance_path) != inv["vendor_provenance_sha256"]:
        raise RuntimeError("Changed reviewed provider provenance")
    actual_vendor = {str(p.relative_to(ROOT / "vendor"))
                     for p in ROOT.glob("vendor/**/*.lean")}
    expected_vendor = {m.replace(".", "/") + ".lean" for m in provider["modules"]}
    if actual_vendor != expected_vendor or actual_vendor != set(provider["files_sha256"]):
        raise RuntimeError("Missing or extra relocated provider modules")
    for module, info in provider["module_sources_and_imports"].items():
        original = (ROOT / "vendor" / info["preserved_upstream_bytes"]).read_bytes()
        if hashlib.sha256(original).hexdigest() != info["upstream_sha256"]:
            raise RuntimeError("Changed preserved upstream bytes: " + module)
        local = ROOT / "vendor" / info["local_path"]
        if sha(local) != provider["files_sha256"][info["local_path"]]:
            raise RuntimeError("Changed local supplier: " + module)
        expected = original
        for patch in info["import_patches"]:
            old, new = patch["old"].encode(), patch["new"].encode()
            if expected.count(old) != patch["occurrences"]:
                raise RuntimeError("Unexpected provider patch count")
            expected = expected.replace(old, new)
        if local.read_bytes() != expected:
            raise RuntimeError("Undeclared supplier modification: " + module)
    if sha(ROOT / "vendor" / provider["license"]["path"]) != provider["license"]["sha256"]:
        raise RuntimeError("Changed supplier license")

    parent_record_path = BASE / inv["parent_verification_path"]
    if sha(parent_record_path) != inv["parent_verification_sha256"]:
        raise RuntimeError("Changed parent CI record")
    parent = json.loads(parent_record_path.read_text())
    if parent["ok"] is not True or parent["full_theorem_1_8_proved"] is not False:
        raise RuntimeError("Parent context is not the accepted foundation milestone")
    for path, digest in parent["input_sha256"].items():
        if sha(BASE / path) != digest:
            raise RuntimeError("Parent context changed after accepted CI: " + path)
    for review in parent["independent_reviews"]:
        path = BASE / "docs/theorem18/reviews" / ("foundations-" + review["reviewer"] + ".json")
        if sha(path) != review["json_sha256"] or sha(path.with_suffix(".md")) != review["markdown_sha256"]:
            raise RuntimeError("Changed historical parent statement review")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    parent_manifest = json.loads((BASE / "lake-manifest.json").read_text())
    parent_pins = {p["name"]: p["rev"] for p in parent_manifest["packages"] if p["type"] == "git"}
    pins = {p["name"]: p["rev"] for p in manifest["packages"] if p["type"] == "git"}
    if pins != parent_pins or (ROOT / "lean-toolchain").read_bytes() != (BASE / "lean-toolchain").read_bytes():
        raise RuntimeError("Landmark toolchain/dependency pins differ from the parent")
    if pins["mathlib"] != provider["project_mathlib_revision"]:
        raise RuntimeError("Supplier mathlib verification pin differs")
    paths = [p for p in manifest["packages"] if p["type"] == "path"]
    if len(paths) != 1 or paths[0]["dir"] != "..":
        raise RuntimeError("Unexpected local parent package")
    record["parent_verified_input_sha256"] = parent["input_sha256"]
    record["parent_verification_sha256"] = inv["parent_verification_sha256"]
    record["independent_reviews"] = []
    expected_declarations = {d["name"] for d in inv["declarations"]}
    for label in ["a", "b"]:
        p = ROOT / "reviews" / ("landmark1-" + label + ".json")
        review = json.loads(p.read_text())
        if review["verdict"] != "accept-landmark1" or review["landmark_1_proved"] is not True:
            raise RuntimeError("Landmark statement review not accepted")
        if review["full_theorem_1_8_proved"] is not False:
            raise RuntimeError("Reviewer claims full-theorem completion")
        if review["model"] != "gpt-6.1-sol" or review["reasoning_effort"] != "high":
            raise RuntimeError("Unexpected independent reviewer configuration")
        expected = {
            "project_source_sha256": actual,
            "configuration_sha256": config,
            "new_provider_source_sha256": provider["files_sha256"],
            "vendor_provenance_sha256": inv["vendor_provenance_sha256"],
            "parent_verification_sha256": inv["parent_verification_sha256"],
        }
        for key, value in expected.items():
            if review[key] != value:
                raise RuntimeError("Stale or incomplete review binding: " + label + ":" + key)
        if set(review["declarations"]) != expected_declarations:
            raise RuntimeError("Incomplete declaration review: " + label)
        record["independent_reviews"].append({
            "reviewer": label, "json_sha256": sha(p), "markdown_sha256": sha(p.with_suffix(".md")),
        })
    return inv, provider, parent


def inputs(parent):
    files = [*ROOT.glob("*.lean"), *ROOT.glob("ArtinLandmarks/**/*.lean"),
             *ROOT.glob("vendor/**/*.lean"), *ROOT.glob("vendor/**/*.lean.txt"),
             *ROOT.glob("scripts/*.py")]
    files += [ROOT / name for name in [
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", "README.md",
        "source-inventory.json", "vendor/provenance.json", "vendor/LICENSE.TauCeti", "vendor/README.md",
    ]]
    files += [BASE / ".github/workflows/landmarks.yml"]
    return {**parent["input_sha256"],
            **{str(p.relative_to(BASE)): sha(p) for p in sorted(set(files))}}


record = {
    "kind": "theorem18-landmark1-verification",
    "scope": "Actual relative normalizer quotient covering and geometric exact sequence only",
    "landmark_1_proved": True,
    "full_theorem_1_8_proved": False,
    "started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "repository_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=BASE, text=True).strip(),
    "commands": [], "ok": False,
}


def save():
    (out / "verification.json").write_text(json.dumps(record, indent=2) + "\n")


save()
try:
    inv, provider, parent = check_bindings()
    record["input_sha256"] = inputs(parent)
    record["source_inventory_sha256"] = sha(ROOT / "source-inventory.json")
    record["vendor_provenance_sha256"] = sha(ROOT / "vendor/provenance.json")
    project_modules = ["ArtinLandmarks." + str(p.relative_to(ROOT / "ArtinLandmarks"))
                       .removesuffix(".lean").replace("/", ".")
                       for p in sorted(ROOT.glob("ArtinLandmarks/**/*.lean"))]
    commands = [
        ("lean-version", ["lean", "--version"]),
        ("lake-version", ["lake", "--version"]),
        ("mathlib-revision", ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]),
        ("clean-landmarks", ["lake", "clean", "artin-landmarks"]),
        ("build-landmark1", ["lake", "build", "ArtinLandmarks"]),
        ("landmark-and-provider-axioms", ["lake", "env", "lean", "-DwarningAsError=true", "LandmarkAudit.lean"]),
        *[("replay-" + module.replace(".", "-"), ["lake", "env", "leanchecker", "--verbose", module])
          for module in provider["modules"] + project_modules],
    ]
    save()
    for label, argv in commands:
        log = out / (label + ".log")
        print("Running:", " ".join(argv), flush=True)
        started = time.monotonic()
        with log.open("w") as stream:
            result = subprocess.run(argv, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
        record["commands"].append({
            "argv": argv, "exit_code": result.returncode, "log": log.name,
            "log_sha256": sha(log), "elapsed_seconds": round(time.monotonic() - started, 3),
        })
        save()
        if result.returncode:
            print(log.read_text(), flush=True)
            raise RuntimeError(label + " failed")
        if label == "landmark-and-provider-axioms":
            expected = set(provider["modules"] + project_modules)
            for p in [BASE / "vendor/provenance.json", BASE / "vendor/theorem18-provenance.json"]:
                expected.update(json.loads(p.read_text())["modules"])
            seen = {line.split()[1] for line in log.read_text().splitlines()
                    if line.startswith("LANDMARK_AXIOMS ")}
            if seen != expected:
                raise RuntimeError("Incomplete or unexpected axiom module coverage: " + str(sorted(seen ^ expected)))
            record["audited_modules"] = sorted(seen)
    if inputs(parent) != record["input_sha256"]:
        raise RuntimeError("Inputs changed during verification")
    before = list(record["independent_reviews"])
    check_bindings()
    if record["independent_reviews"] != before:
        raise RuntimeError("Reviews changed during verification")
    if (out / "mathlib-revision.log").read_text().strip() != provider["project_mathlib_revision"]:
        raise RuntimeError("Actual mathlib checkout differs from verification pin")
    record["ok"] = True
except Exception as exc:
    record["error"] = str(exc)
    raise
finally:
    record["finished_at"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save()
print("Landmark 1 verified: actual quotient covering and geometric exact sequence. Full Theorem 1.8 remains unproved.", flush=True)
