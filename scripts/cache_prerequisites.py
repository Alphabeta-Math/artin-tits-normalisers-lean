#!/usr/bin/env python3
"""Fetch only the pinned mathlib imports used by the project and vendored sources."""
from pathlib import Path
import os
import re
import subprocess

root = Path(__file__).resolve().parents[1]
files = [*root.glob("*.lean"), *root.glob("ArtinNormalisers/**/*.lean"),
         *root.glob("vendor/**/*.lean")]
pattern = r"^(?:(?:public|meta)\s+)*import(?:\s+all)?\s+(Mathlib\.[\w.]+)"
modules = sorted({name for file in files
                  for name in re.findall(pattern, file.read_text(), re.MULTILINE)})
if not modules:
    raise SystemExit("No mathlib imports selected")
env = dict(os.environ)
env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
print("Caching pinned dependency closure:", ", ".join(modules), flush=True)
subprocess.run(["lake", "exe", "cache", "get", *modules], cwd=root, env=env, check=True)
