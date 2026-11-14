#!/usr/bin/env python3
"""Reproduce the root-selected, byte-exact two-declaration TauCeti extraction."""

import argparse
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
VENDOR = ROOT / "vendor"
ORIGINAL = "upstream-original/TauCeti/AlgebraicTopology/FundamentalGroup/BasepointChange.lean.txt"
ACTIVE = "ArtinSequenceVendor/FundamentalGroup/BasepointChange.lean"
PATCH = "patches/ArtinSequenceVendor/FundamentalGroup/BasepointChange.lean.patch"
MODULE = "ArtinSequenceVendor.FundamentalGroup.BasepointChange"
UPSTREAM_SHA = "62bbc0596dc3539d488232e4e924a338548ea0a9"
ORIGINAL_SHA256 = "87851dc988d7b53b32c35841a90f22aae58f3cd0eb6a4f3e232e78fc69b3bc43"
BLOCKS = [
    ("FundamentalGroup.fundamentalGroupMulEquivOfPath_apply", 129, 148),
    ("FundamentalGroup.map_fundamentalGroupMulEquivOfPath", 196, 212),
]
IMPORTS = [
    "Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup",
    "Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps",
]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def products():
    original = (VENDOR / ORIGINAL).read_bytes()
    assert digest(original) == ORIGINAL_SHA256
    lines = original.splitlines(keepends=True)
    assert len(lines) == 651
    blocks = [b"".join(lines[start - 1:end]) for _, start, end in BLOCKS]
    header = b"".join(lines[:7])
    wrapper = (
        "\n".join("public import " + name for name in IMPORTS)
        + "\n\n/-!\n"
        + "# Two exact TauCeti basepoint-change declarations\n\n"
        + "Extracted on 2026-11-14 from TauCeti at " + UPSTREAM_SHA + ".\n"
        + "This file changes only the module wrapper/imports and omits unrelated declarations.\n"
        + "Both selected declaration blocks are retained byte for byte; the complete original,\n"
        + "line locators, hashes and assembly recipe are preserved beside this source.\n"
        + "-/\n\npublic section\n\nnamespace FundamentalGroup\n\n"
    ).encode()
    active = header + wrapper + blocks[0] + b"\n" + blocks[1] + b"\nend FundamentalGroup\n"
    patch = "".join(difflib.unified_diff(
        original.decode().splitlines(keepends=True),
        active.decode().splitlines(keepends=True),
        fromfile="a/TauCeti/AlgebraicTopology/FundamentalGroup/BasepointChange.lean",
        tofile="b/" + ACTIVE,
    )).encode()
    recipe = {
        "schema_version": 1,
        "kind": "verbatim-declaration-extraction",
        "original_path": ORIGINAL,
        "original_sha256": digest(original),
        "copyright_header_original_lines": [1, 5],
        "module_line_original": 6,
        "namespace": "FundamentalGroup",
        "public_section": True,
        "imports": IMPORTS,
        "selected_blocks": [
            {"name": name, "start_line": start, "end_line": end,
             "sha256": digest(block), "bytes": len(block),
             "declaration_and_proof_unchanged": True}
            for (name, start, end), block in zip(BLOCKS, blocks)
        ],
        "active_path": ACTIVE,
        "active_sha256": digest(active),
        "patch_path": PATCH,
        "patch_sha256": digest(patch),
        "hypothesis_changes": [],
        "proof_body_changes": [],
        "wrapper_changes": ["minimal Mathlib imports", "new module path",
                            "extraction notice", "unrelated declarations omitted"],
    }
    script_path = "scripts/providers/assemble.py"
    recipe_bytes = (json.dumps(recipe, indent=2) + "\n").encode()
    provenance = {
        "schema_version": 1,
        "repository": "https://github.com/TauCetiProject/TauCeti",
        "upstream_sha": UPSTREAM_SHA,
        "upstream_mathlib_revision": "e8ba86fa9744dd8d90f48c1752bc735f61a4ca81",
        "project_mathlib_revision": "65d730f7150f21fdfa32f3e73a3f549c1f96a0e9",
        "lean_toolchain": "leanprover/lean4:v4.36.0-rc2",
        "extraction_kind": "two exact declaration blocks; no proof/hypothesis changes",
        "selection_status": "root-selected; independent reviews and root acceptance pending",
        "topological_order": [MODULE],
        "license": {"path": "LICENSE.TauCeti", "identifier": "Apache-2.0",
                    "sha256": digest((VENDOR / "LICENSE.TauCeti").read_bytes())},
        "assembly_script": script_path,
        "assembly_script_sha256": digest((ROOT / script_path).read_bytes()),
        "assembly_recipe": "extraction-recipe.json",
        "assembly_recipe_sha256": digest(recipe_bytes),
        "files": [{
            "module": MODULE,
            "path": ACTIVE,
            "active_sha256": digest(active),
            "upstream_module": "TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange",
            "upstream_path": "TauCeti/AlgebraicTopology/FundamentalGroup/BasepointChange.lean",
            "original_path": ORIGINAL,
            "upstream_sha256": digest(original),
            "patch_path": PATCH,
            "patch_sha256": digest(patch),
            "selected_blocks": recipe["selected_blocks"],
            "imports": IMPORTS,
            "application": "Canonical path-conjugation formula and induced-map/basepoint square for landmark 4",
        }],
        "new_non_mathlib_imports": [],
        "full_upstream_recursive_closure_imported": False,
        "full_landmark_4_proved": False,
        "full_theorem_1_8_proved": False,
    }
    encode = lambda obj: (json.dumps(obj, indent=2) + "\n").encode()
    return {VENDOR / ACTIVE: active, VENDOR / PATCH: patch,
            VENDOR / "extraction-recipe.json": encode(recipe),
            VENDOR / "provenance.json": encode(provenance)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for path, data in products().items():
        if args.check:
            assert path.read_bytes() == data, f"Assembly mismatch: {path}"
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
    print("Exact two-declaration assembly verified" if args.check else "Exact two-declaration assembly written")


if __name__ == "__main__":
    main()
