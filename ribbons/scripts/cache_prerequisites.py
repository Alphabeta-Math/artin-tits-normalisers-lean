#!/usr/bin/env python3
"""Fetch the whole pinned Mathlib closure required by the OAI provider imports.

Uses the committed child manifest and checks its inherited dependencies against
the parent manifest. It does not run `lake update` or edit package configuration.
The gitignored dependency directory may be shared with the parent checkout.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT.parent


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_packages(manifest: dict) -> dict[str, dict]:
    return {p["name"].strip("«»"): p for p in manifest["packages"]
            if p["type"] == "git"}


def check_checkout(package: Path, expected: str) -> None:
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=package, text=True).strip()
    if revision != expected:
        raise RuntimeError(f"{package}: expected {expected}, found {revision}")
    changes = subprocess.check_output(
        ["git", "status", "--porcelain", "--untracked-files=no"],
        cwd=package, text=True).strip()
    if changes:
        raise RuntimeError(f"Tracked dependency changes in {package}:\n{changes}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true",
                        help="show the validated pins and command without fetching or writing")
    args = parser.parse_args()
    protected = [directory / name for directory in (ROOT, PARENT)
                 for name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json")]
    before = {str(p): sha256(p) for p in protected}
    parent_manifest = json.loads((PARENT / "lake-manifest.json").read_text())
    child_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    parent_packages = git_packages(parent_manifest)
    packages = git_packages(child_manifest)
    if set(parent_packages) != set(packages):
        raise RuntimeError("The child and parent git dependency inventories differ")
    for name, package in packages.items():
        parent = parent_packages[name]
        if package["rev"] != parent["rev"] or package["url"].removesuffix(".git") != parent["url"].removesuffix(".git"):
            raise RuntimeError(f"Inherited parent pin differs for {name}")
    path_dependencies = [p for p in child_manifest["packages"] if p["type"] == "path"]
    if len(path_dependencies) != 1 or (ROOT / path_dependencies[0]["dir"]).resolve() != PARENT:
        raise RuntimeError("The ribbons path dependency is not this checkout's parent")
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    if toolchain != (PARENT / "lean-toolchain").read_text().strip():
        raise RuntimeError("The ribbons and parent Lean toolchains differ")
    command = ["lake", "exe", "cache", "get", "Mathlib"]
    plan = {"toolchain": toolchain, "mathlib_revision": packages["mathlib"]["rev"],
            "git_dependencies": {n: p["rev"] for n, p in packages.items()},
            "command": command, "cwd": str(ROOT),
            "cache_scope": "whole Mathlib import closure, including its pinned prerequisites",
            "package_configuration_changes": False}
    print(json.dumps(plan, indent=2), flush=True)
    if args.plan:
        return

    # Never replace an existing cache directory or symlink. On a fresh checkout,
    # this relative link shares the parent cache without embedding a machine path.
    parent_cache = PARENT / parent_manifest["packagesDir"]
    parent_cache.mkdir(parents=True, exist_ok=True)
    (ROOT / ".lake").mkdir(exist_ok=True)
    local_cache = ROOT / child_manifest["packagesDir"]
    if not local_cache.exists() and not local_cache.is_symlink():
        local_cache.symlink_to(os.path.relpath(parent_cache, local_cache.parent),
                               target_is_directory=True)
    if not local_cache.is_dir():
        raise RuntimeError(f"Dependency cache is unavailable: {local_cache}")
    for name, package in packages.items():
        checkout = local_cache / name
        if checkout.exists():
            check_checkout(checkout, package["rev"])
    env = dict(os.environ)
    elan_bin = Path.home() / ".elan/bin"
    if elan_bin.is_dir():
        env["PATH"] = str(elan_bin) + os.pathsep + env.get("PATH", "")
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    subprocess.run(command, cwd=ROOT, env=env, check=True)
    for name, package in packages.items():
        check_checkout(local_cache / name, package["rev"])
    after = {str(p): sha256(p) for p in protected}
    if after != before:
        raise RuntimeError("Package configuration or a locked manifest changed while caching")
    print("Pinned whole-Mathlib cache fetched; package configuration unchanged.", flush=True)


if __name__ == "__main__":
    main()
