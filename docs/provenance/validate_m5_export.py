#!/usr/bin/env python3
"""Check the complete M5 prerequisite record and source-attribution supplement, without Lean.

This is record/graph integrity verification only. It does not replay a kernel,
review mathematical statements, rewrite graphs, or claim clean CI has passed.
"""

from __future__ import annotations
import argparse, gzip, hashlib, json, subprocess
from pathlib import Path

BASE = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return digest(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text())


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def decode(info):
    path = BASE / info["path"]
    compressed = path.read_bytes()
    require(
        digest(compressed) == info["compressed_sha256"],
        "Compressed hash mismatch: " + str(path),
    )
    data = gzip.decompress(compressed)
    require(
        digest(data) == info["uncompressed_sha256"]
        and len(data) == info["uncompressed_bytes"],
        "Uncompressed hash/length mismatch: " + str(path),
    )
    return json.loads(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, default=OUT / "m5/run-20261114T090600Z")
    parser.add_argument("--output", type=Path, default=OUT / "m5/validation.json")
    args = parser.parse_args()
    run = args.run.resolve()
    execution_path = run / "execution.json"
    e = read(execution_path)
    baseline_before = {name: sha(OUT / name) for name in e["baseline_sha256_before"]}
    require(
        e["ok"] is True
        and e["inputs_unchanged"] is True
        and e["baseline_unchanged"] is True
        and e["old_roots_and_dependency_edges_preserved"] is True,
        "Export record did not pass",
    )
    require(
        e["final_observer_inputs_sha256_before"]
        == e["final_observer_inputs_sha256_after"],
        "Export input snapshots differ",
    )
    require(
        e["baseline_sha256_before"] == e["baseline_sha256_after"] == baseline_before,
        "Historical baseline archive changed",
    )
    for command in e["commands"]:
        require(command["exit_code"] == 0, "Export command failed")
        require(
            sha(BASE / command["log"]) == command["log_sha256"],
            "Export raw command log changed",
        )
    raw = [decode(info) for info in e["raw_graphs"]]
    require(len(raw) == 2 and raw[0] == raw[1], "Preliminary/final raw graphs differ")
    original = raw[1]
    graph = decode(e["annotated_graph"])
    for key, value in original.items():
        other = graph[key]
        if key == "nodes":
            other = [{k: v for k, v in node.items() if k != "source"} for node in other]
        require(value == other, "Annotated graph dropped/changed raw data: " + key)
    nodes = {n["name"]: n for n in graph["nodes"]}
    roots = set(graph["roots"])
    require(
        len(nodes) == len(graph["nodes"]) == graph["declaration_count"],
        "Duplicate/missing node names",
    )
    require(len(roots) == len(graph["roots"]), "Duplicate project roots")
    require(
        roots == {n["name"] for n in graph["nodes"] if n["is_project_root"]},
        "Project-root flags differ",
    )
    edge_count = 0
    for name, node in nodes.items():
        refs = set(
            node["type_dependencies"]
            + node["value_dependencies"]
            + node["structural_dependencies"]
        )
        edge_count += len(refs)
        require(refs <= nodes.keys(), "Dangling dependency reference: " + name)
        require(
            node["module"] in graph["module_sources"]
            and node["source"] == graph["module_sources"][node["module"]],
            "Node/source attribution differs: " + name,
        )
    require(
        edge_count == graph["edge_count"] == e["counts"]["references"],
        "Reference count differs",
    )
    physical = graph["physical_project_modules"]
    occurrences = [(row["module"], name) for row in physical for name in row["names"]]
    physical_names = {name for _, name in occurrences}
    aliases = graph["physical_project_identical_theorem_aliases"]
    require(
        physical_names == roots
        and len(occurrences) == graph["physical_project_occurrences"],
        "Physical project coverage differs",
    )
    physical_modules = {r["module"] for r in physical}
    external_owner_aliases = [
        a for a in aliases if a["canonical_module"] not in physical_modules
    ]
    require(
        len(occurrences) == len(roots) + len(aliases) - len(external_owner_aliases),
        "Physical/unique/project-duplicate/external-owner counts differ",
    )
    for alias in aliases:
        require(
            (alias["physical_module"], alias["name"]) in occurrences,
            "Alias physical occurrence absent",
        )
        require(
            nodes[alias["name"]]["module"] == alias["canonical_module"],
            "Alias canonical owner differs",
        )
        require(
            all(
                alias[key] is True
                for key in ["same_type", "same_proof", "same_universe_parameters"]
            ),
            "Alias lacks exact proof/type/universe equality",
        )
    inventory = read(BASE / "asphericity/source-inventory.json")
    require(
        sha(BASE / "asphericity/source-inventory.json") == e["source_inventory_sha256"],
        "Frozen M5 prerequisite inventory changed",
    )
    newphysical = {
        row["module"]: sorted(row["names"])
        for row in physical
        if row["module"] == "ArtinAsphericity"
        or row["module"].startswith("ArtinAsphericity.")
    }
    require(
        newphysical == inventory["compiled_declaration_occurrences_by_module"],
        "M5 prerequisite physical inventory differs",
    )
    baseline = json.loads(
        gzip.decompress((OUT / "m4/run-20261114T080416Z/graph.json.gz").read_bytes())
    )
    old_roots = set(baseline["roots"])
    new_physical = {name for names in newphysical.values() for name in names}
    require(
        roots == old_roots | new_physical,
        "Project union lost or added unexplained roots",
    )
    for old in baseline["nodes"]:
        require(old["name"] in nodes, "Old reachable declaration was dropped")
        for key in [
            "kind",
            "has_value",
            "type_dependencies",
            "value_dependencies",
            "structural_dependencies",
        ]:
            require(
                old[key] == nodes[old["name"]][key],
                "Old dependency content changed: " + old["name"],
            )
    overlap = old_roots & new_physical
    require(
        len(roots) == len(old_roots) + len(new_physical) - len(overlap),
        "Old/new root union accounting differs",
    )
    shared = sorted({a["name"] for a in aliases})
    head = e["observed_git_head"]
    tree_command = ["git", "ls-tree", "-r", "--full-tree", "--name-only", head]
    tree_raw = subprocess.check_output(tree_command, cwd=BASE)
    tree = set(tree_raw.decode().splitlines())
    commands = [
        {
            "argv": tree_command,
            "cwd": "repository root",
            "exit_code": 0,
            "stdout_sha256": digest(tree_raw),
        }
    ]
    project = {
        m: s
        for m, s in graph["module_sources"].items()
        if s["repository"]
        == "https://github.com/lazyinspirit/artin-tits-normalisers-lean"
    }
    committed, precommit = 0, 0
    for module, source in project.items():
        path = source["source_path"]
        if source["exact_bytes_at_observed_head"]:
            require(path in tree, "Published project source absent: " + module)
            argv = ["git", "cat-file", "blob", head + ":" + path]
            blob = subprocess.check_output(argv, cwd=BASE)
            commands.append(
                {
                    "argv": argv,
                    "cwd": "repository root",
                    "exit_code": 0,
                    "stdout_sha256": digest(blob),
                }
            )
            require(
                digest(blob) == source["source_sha256"],
                "Published blob differs: " + module,
            )
            require(
                source["github_blob_url"]
                == "https://github.com/lazyinspirit/artin-tits-normalisers-lean/blob/"
                + head
                + "/"
                + path,
                "Wrong publication URL",
            )
            committed += 1
        else:
            require(
                "github_blob_url" not in source,
                "Uncommitted source has fabricated publication URL",
            )
            require(
                sha(BASE / path) == source["source_sha256"],
                "Precommit source snapshot changed",
            )
            if path in tree:
                argv = ["git", "cat-file", "blob", head + ":" + path]
                blob = subprocess.check_output(argv, cwd=BASE)
                commands.append(
                    {
                        "argv": argv,
                        "cwd": "repository root",
                        "exit_code": 0,
                        "stdout_sha256": digest(blob),
                    }
                )
                require(
                    digest(blob) != source["source_sha256"],
                    "Exact published source mislabeled precommit",
                )
            precommit += 1
    require(
        all(
            inventory[k] is False
            for k in [
                "full_landmark_5_proved",
                "actual_arrangement_asphericity_proved",
                "full_theorem_1_8_proved",
            ]
        ),
        "Inventory overstates prerequisite scope",
    )
    result = {
        "full_landmark_5_proved": False,
        "actual_arrangement_asphericity_proved": False,
        "full_theorem_1_8_proved": False,
        "accepted_asphericity_prerequisites": False,
        "kind": "complete-M5 prerequisite-graph-and-attribution-integrity",
        "ok": True,
        "run_execution_sha256": sha(execution_path),
        "annotated_graph_sha256": e["annotated_graph"]["compressed_sha256"],
        "source_attribution": "Actual full-tree/blob checks for published sources; exact source snapshot hashes with no false links for uncommitted source bytes",
        "validator_sha256": sha(Path(__file__)),
        "counts": e["counts"],
        "edges_have_targets": True,
        "all_raw_data_preserved_in_annotation": True,
        "old_roots_and_edges_preserved": True,
        "M5 prerequisite_physical_inventory_matches_frozen_audit": True,
        "shared_name": shared,
        "external_canonical_owner_aliases": external_owner_aliases,
        "physical_accounting": "physical occurrences = distinct roots + alias rows - aliases whose canonical owner has no project physical occurrence",
        "old_roots": len(old_roots),
        "technical_prerequisite_physical_distinct_names": len(new_physical),
        "shared_names": sorted(overlap),
        "exact_committed_modules_at_observed_HEAD": committed,
        "precommit_modules_at_observed_HEAD": precommit,
        "attribution_git_commands": commands,
        "baseline_archive_sha256_before": baseline_before,
        "baseline_archive_sha256_after": {
            name: sha(OUT / name) for name in baseline_before
        },
        "Lean_build_audit_or_kernel_replay_executed": False,
        "clean_github_ci_status": "pending/in progress; no successful CI result asserted",
        "limits": "Record integrity, complete graph/occurrence accounting and actual Git source-attribution validation only; mathematical acceptance is the separate root receipt.",
    }
    require(
        result["baseline_archive_sha256_before"]
        == result["baseline_archive_sha256_after"],
        "Baseline changed during metadata validation",
    )
    require(
        not args.output.exists(),
        "Refuse to overwrite existing validation; select another --output",
    )
    write = Path(args.output)
    write.parent.mkdir(parents=True, exist_ok=True)
    write.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "ok": True,
                "output": str(write),
                "counts": e["counts"],
                "observed_source_attribution": [committed, precommit],
                "no_Lean_commands": True,
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
