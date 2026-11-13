#!/usr/bin/env python3
"""Fetch the pinned mathlib import closure for the parent and landmark package."""
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT.parent
cache = PARENT / ".lake/packages"
cache.mkdir(parents=True, exist_ok=True)
(ROOT / ".lake").mkdir(exist_ok=True)
local = ROOT / ".lake/packages"
if not local.exists() and not local.is_symlink():
    local.symlink_to(cache, target_is_directory=True)

files = [*PARENT.glob("*.lean"), *PARENT.glob("ArtinNormalisers/**/*.lean"),
         *PARENT.glob("vendor/**/*.lean"), *ROOT.glob("*.lean"),
         *ROOT.glob("ArtinLandmarks/**/*.lean"), *ROOT.glob("vendor/ArtinLandmarkVendor/**/*.lean")]
pattern = r"^(?:(?:public|meta)\s+)*import(?:\s+all)?\s+(Mathlib\.[\w.]+)"
modules = sorted({m for p in files for m in re.findall(pattern, p.read_text(), re.MULTILINE)})
if not modules:
    raise SystemExit("No prerequisite modules selected")
env = dict(os.environ)
env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
print("Fetching pinned import closure:", ", ".join(modules), flush=True)
subprocess.run(["lake", "exe", "cache", "get", *modules], cwd=ROOT, env=env, check=True)
