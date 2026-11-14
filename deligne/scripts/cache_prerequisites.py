#!/usr/bin/env python3
"""Fetch committed pinned Mathlib cache for deligne and its seven path packages.

--plan is read-only. No lake update, lock/config rewrite, or scientific source
mutation is performed. Whole Mathlib is required by the frozen OAI imports.
"""

from __future__ import annotations
import argparse, hashlib, json, os, subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT.parent
DIRECTORIES = [
    BASE,
    BASE / "ribbons",
    BASE / "landmarks",
    BASE / "chambers",
    BASE / "sequences",
    BASE / "asphericity",
    BASE / "homotopy",
    ROOT,
]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git_packages(m):
    return {p["name"].strip("«»"): p for p in m["packages"] if p["type"] == "git"}


def check_checkout(path, revision):
    actual = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=path, text=True
    ).strip()
    if actual != revision:
        raise RuntimeError(f"Wrong Git pin: {path}: {actual} != {revision}")
    changes = subprocess.check_output(
        ["git", "status", "--porcelain", "--untracked-files=no"], cwd=path, text=True
    ).strip()
    if changes:
        raise RuntimeError(f"Tracked dependency changes in {path}:\n{changes}")


def validate():
    manifests = {
        d: json.loads((d / "lake-manifest.json").read_text()) for d in DIRECTORIES
    }
    packages = git_packages(manifests[BASE])
    toolchain = (BASE / "lean-toolchain").read_bytes()
    for directory, manifest in manifests.items():
        actual = git_packages(manifest)
        if set(actual) != set(packages):
            raise RuntimeError(f"Git dependency set differs: {directory}")
        for name, p in actual.items():
            if p["rev"] != packages[name]["rev"] or p["url"].removesuffix(
                ".git"
            ) != packages[name]["url"].removesuffix(".git"):
                raise RuntimeError(f"Inherited Git pin differs: {directory}: {name}")
        if (directory / "lean-toolchain").read_bytes() != toolchain:
            raise RuntimeError(f"Toolchain differs: {directory}")
    names = [
        "artin-normalisers",
        "artin-ribbons",
        "artin-landmarks",
        "artin-chambers",
        "artin-sequences",
        "artin-asphericity",
        "artin-homotopy",
        "artin-deligne",
    ]
    for index, directory in enumerate(DIRECTORIES):
        expected = dict(zip(names[:index], DIRECTORIES[:index]))
        if directory == BASE / "landmarks":
            expected = {"artin-normalisers": BASE}
        actual = {
            p["name"].strip("«»"): (directory / p["dir"]).resolve()
            for p in manifests[directory]["packages"]
            if p["type"] == "path"
        }
        if actual != {name: path.resolve() for name, path in expected.items()}:
            raise RuntimeError(
                f"Unexpected inherited path packages: {directory}: {actual}"
            )
    return manifests, packages


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    args = parser.parse_args()
    protected = [
        d / n
        for d in DIRECTORIES
        for n in ["lakefile.toml", "lean-toolchain", "lake-manifest.json"]
    ]
    before = {str(p.relative_to(BASE)): digest(p) for p in protected}
    manifests, packages = validate()
    command = ["lake", "exe", "cache", "get", "Mathlib"]
    print(
        json.dumps(
            {
                "kind": "deligne-pinned-cache-plan",
                "git_pins": {
                    n: {"repository": p["url"], "revision": p["rev"]}
                    for n, p in packages.items()
                },
                "resolved_path_packages": {
                    p["name"]: str((ROOT / p["dir"]).resolve())
                    for p in manifests[ROOT]["packages"]
                    if p["type"] == "path"
                },
                "command": command,
                "cwd": str(ROOT),
                "scope": "whole pinned Mathlib import closure; no mathematical verification claimed",
                "protected_configuration_sha256": before,
                "lake_update": False,
            },
            indent=2,
        ),
        flush=True,
    )
    if args.plan:
        return
    shared = BASE / manifests[BASE]["packagesDir"]
    shared.mkdir(parents=True, exist_ok=True)
    for directory in DIRECTORIES[1:]:
        (directory / ".lake").mkdir(exist_ok=True)
        cache = directory / manifests[directory]["packagesDir"]
        if not cache.exists() and not cache.is_symlink():
            cache.symlink_to(
                os.path.relpath(shared, cache.parent), target_is_directory=True
            )
        if not cache.is_dir():
            raise RuntimeError(f"Cache unavailable: {cache}")
    for name, p in packages.items():
        if (shared / name).exists():
            check_checkout(shared / name, p["rev"])
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    subprocess.run(command, cwd=ROOT, env=env, check=True)
    for name, p in packages.items():
        check_checkout(shared / name, p["rev"])
    if before != {str(p.relative_to(BASE)): digest(p) for p in protected}:
        raise RuntimeError("Protected manifest/configuration changed")
    print(
        "Pinned full Mathlib cache available; all eight package configurations unchanged.",
        flush=True,
    )


if __name__ == "__main__":
    main()
