#!/usr/bin/env python3
"""Check the complete M4 record and source-attribution supplement, without Lean.

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
    parser.add_argument("--run", type=Path, default=OUT / "m4/run-20261114T080416Z")
    parser.add_argument("--output", type=Path, default=OUT / "m4/validation.json")
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
    require(
        len(occurrences) == len(roots) + len(aliases),
        "Physical/unique/alias counts differ",
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
    inventory = read(BASE / "sequences/source-inventory.json")
    require(
        sha(BASE / "sequences/source-inventory.json") == e["source_inventory_sha256"],
        "Frozen M4 inventory changed",
    )
    m3physical = {
        row["module"]: sorted(row["names"])
        for row in physical
        if row["module"] == "ArtinSequences"
        or row["module"].startswith("ArtinSequences.")
    }
    require(
        m3physical == inventory["compiled_declaration_occurrences_by_module"],
        "M4 physical inventory differs",
    )
    baseline = json.loads(
        gzip.decompress((OUT / "m3/run-20261114T065009Z/graph.json.gz").read_bytes())
    )
    old_roots = set(baseline["roots"])
    new_physical = {name for names in m3physical.values() for name in names}
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
        len(old_roots) == 2375
        and len(new_physical) == 151
        and not overlap
        and len(roots) == 2526
        and len(occurrences) == 2528
        and len(aliases) == 2,
        "Recorded M3+M4 root/physical accounting differs",
    )
    shared = "ArtinNormalisers.Ribbon2.elementaryMu.congr_simp"
    require({a["name"] for a in aliases} == {shared}, "Unexpected alias theorem")
    require(
        {a["physical_module"] for a in aliases}
        == {"ArtinRibbons.RibbonWords", "ArtinChambers.PositiveTransport"},
        "Historical alias occurrence modules differ",
    )
    head = e["observed_git_head"]
    require(
        head == "e7703926f3e486c0fca3a0fe292ab56d6411c248",
        "Unexpected M4 source observation commit",
    )
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
    for module, source in project.items():
        path = source["source_path"]
        require(
            path in tree and source["exact_bytes_at_observed_head"] is True,
            "Published project source mislabeled: " + module,
        )
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
            "Actual published source blob differs: " + module,
        )
        require(
            source["github_blob_url"]
            == "https://github.com/lazyinspirit/artin-tits-normalisers-lean/blob/"
            + head
            + "/"
            + path,
            "Wrong project publication URL",
        )
    require(len(project) == 91, "Unexpected complete project module-source count")
    result = {
        "kind": "complete-M4-graph-and-attribution-integrity",
        "ok": True,
        "run_execution_sha256": sha(execution_path),
        "annotated_graph_sha256": e["annotated_graph"]["compressed_sha256"],
        "source_attribution": "Direct full-tree published source blob checks; no correction supplement needed",
        "validator_sha256": sha(Path(__file__)),
        "counts": e["counts"],
        "edges_have_targets": True,
        "all_raw_data_preserved_in_annotation": True,
        "old_roots_and_edges_preserved": True,
        "M4_physical_inventory_matches_frozen_audit": True,
        "shared_name": shared,
        "old_roots": 2375,
        "technical_M4_physical_distinct_names": 151,
        "shared_names": 0,
        "exact_committed_modules_at_observed_HEAD": 91,
        "precommit_modules_at_observed_HEAD": 0,
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
                "observed_source_attribution": [91, 0],
                "no_Lean_commands": True,
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
