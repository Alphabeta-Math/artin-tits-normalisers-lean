#!/usr/bin/env python3
"""Write a separate, immutable M3 compiled dependency observation.

Default is a read-only plan. --execute requires the successful frozen technical
record and root source inventory. It does not build, audit, replay, change any
Lake configuration, or confer mathematical acceptance. Two observer passes bind
all actual reachable source/object parts before the final pass. Every attempt
has a unique output directory; the historical through-M2 artifacts are read only.
"""

from __future__ import annotations
import argparse, datetime as dt, gzip, hashlib, json, os, shutil, subprocess, time
from pathlib import Path

BASE = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
CHAMBERS = BASE / "chambers"
LAKE = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
BASELINE_FILES = [
    "dependency-graph.json.gz",
    "dependency-graph.raw.json.gz",
    "export-execution.json",
    "export-execution-initial.json",
    "export-final.log",
    "export-attempt-1.log",
    "export-attempt-2.log",
    "export-attempt-3.log",
    "ExportDependencies.lean",
    "run_export.py",
]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, data):
    Path(path).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def read(path):
    return json.loads(Path(path).read_text())


def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def snapshot(paths):
    return {str(Path(p).resolve()): sha(p) for p in sorted(set(map(Path, paths)))}


def compress(path):
    b = Path(path).read_bytes()
    target = Path(str(path) + ".gz")
    with gzip.GzipFile(filename=str(target), mode="wb", mtime=0) as f:
        f.write(b)
    info = {
        "path": str(target.relative_to(BASE)),
        "compressed_sha256": sha(target),
        "uncompressed_sha256": hashlib.sha256(b).hexdigest(),
        "uncompressed_bytes": len(b),
    }
    Path(path).unlink()
    return info


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--technical-record", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    technical_path = args.technical_record.resolve()
    technical = read(technical_path)
    inventory_path = CHAMBERS / "source-inventory.json"
    inventory = read(inventory_path)
    require(
        technical["ok"] is True and technical["inputs_unchanged"] is True,
        "Technical record is incomplete/failed",
    )
    require(
        inventory["technical_verification_sha256"] == sha(technical_path),
        "Inventory refers to another technical record",
    )
    for key in [
        "project_source_sha256",
        "configuration_sha256",
        "vendor_provenance_sha256",
        "provider_active_source_sha256",
        "provider_original_source_sha256",
        "provider_import_patch_sha256",
    ]:
        require(
            inventory[key] == technical["source_bindings"][key],
            "Technical/source inventory differs: " + key,
        )
    for key in [
        "project_source_sha256",
        "configuration_sha256",
        "provider_active_source_sha256",
        "provider_original_source_sha256",
        "provider_import_patch_sha256",
        "verification_source_sha256",
    ]:
        for path, h in inventory[key].items():
            require(sha(BASE / path) == h, "Frozen source/tooling changed: " + path)
    ledger = read(OUT / "GITHUB-PROOF-SOURCES.json")
    baseline_before = {name: sha(OUT / name) for name in BASELINE_FILES}
    output = (
        args.output
        or OUT / "m3" / dt.datetime.now(dt.timezone.utc).strftime("run-%Y%m%dT%H%M%SZ")
    ).resolve()
    plan = {
        "kind": "M3-compiled-dependency-export-plan",
        "output": str(output),
        "technical_record": str(technical_path),
        "source_inventory_sha256": sha(inventory_path),
        "project_sources": len(inventory["project_source_sha256"]),
        "root_scope": "All canonical and physical project declarations in ArtinNormalisers, ArtinLandmarks, ArtinRibbons, ArtinChambers; suppliers through actual type/value/structural references. Private/generated names included.",
        "baseline_policy": "Never rewrite any through-M2 graph or execution/source record.",
        "no_build_audit_or_kernel_replay": True,
        "configuration_changes": False,
        "mathematical_acceptance_claimed": False,
        "execute": args.execute,
    }
    if not args.execute:
        print(json.dumps(plan, indent=2))
        return 0
    output.mkdir(parents=True, exist_ok=False)
    (output / "logs").mkdir()
    record = {
        **plan,
        "ok": False,
        "started_at": utc(),
        "commands": [],
        "baseline_sha256_before": baseline_before,
        "limitations": [
            "Read-only compiled expression/physical-part observation, not a new statement review, axiom audit or kernel replay.",
            "Canonical name nodes represent identical theorem aliases once; project physical occurrences are explicitly compared and retained. Existing supplier physical duplicates retain their separate accepted coverage records.",
            "Project sources may be uncommitted at observed HEAD. Exact SHA256 snapshots are authoritative; no blob link is emitted for absent/changed Git blobs.",
            "No fresh replay of all Mathlib or old accepted suppliers is claimed.",
        ],
    }

    def save():
        write(output / "execution.json", record)

    def run(label, argv, environment=None):
        log = output / "logs" / (label + ".log")
        t = time.monotonic()
        with log.open("wb") as f:
            p = subprocess.run(
                argv, cwd=CHAMBERS, env=environment, stdout=f, stderr=subprocess.STDOUT
            )
        row = {
            "argv": argv,
            "cwd": "chambers",
            "exit_code": p.returncode,
            "log": str(log.relative_to(BASE)),
            "log_sha256": sha(log),
            "elapsed_seconds": round(time.monotonic() - t, 6),
        }
        record["commands"].append(row)
        save()
        require(p.returncode == 0, label + " failed")
        return log.read_text()

    save()
    raw_paths = []
    try:
        head = run("observed-git-head", ["git", "rev-parse", "HEAD"]).strip()
        record["observed_git_head"] = head
        tree = set(
            run(
                "observed-git-tree", ["git", "ls-tree", "-r", "--name-only", head]
            ).splitlines()
        )
        prefix = Path(
            run("lean-prefix", [LAKE, "env", "lean", "--print-prefix"]).strip()
        )
        record["lean_version"] = run(
            "lean-version", [LAKE, "env", "lean", "--version"]
        ).strip()
        lean_path = run("lean-path", [LAKE, "env", "printenv", "LEAN_PATH"]).strip()
        search = [
            Path(p) if Path(p).is_absolute() else CHAMBERS / p
            for p in lean_path.split(os.pathsep)
        ]
        packages = []
        for package in read(CHAMBERS / "lake-manifest.json")["packages"]:
            if package["type"] != "git":
                continue
            path = CHAMBERS / ".lake/packages" / package["name"]
            actual = run(
                "pin-" + package["name"], ["git", "-C", str(path), "rev-parse", "HEAD"]
            ).strip()
            require(
                actual == package["rev"], "Dependency pin differs: " + package["name"]
            )
            require(
                not run(
                    "tracked-" + package["name"],
                    [
                        "git",
                        "-C",
                        str(path),
                        "status",
                        "--porcelain",
                        "--untracked-files=no",
                    ],
                ).strip(),
                "Dirty dependency: " + package["name"],
            )
            packages.append((path.resolve(), package))
        paths = {
            Path(__file__),
            OUT / "ExportM3Dependencies.lean",
            OUT / "GITHUB-PROOF-SOURCES.json",
            inventory_path,
            technical_path,
            technical_path.parent / "inputs.json",
            technical_path.parent / "project-coverage.json",
        }
        paths.update(BASE / p for p in technical["accepted_context_input_sha256"])
        for candidate in [
            BASE / "docs/theorem18/landmarks/milestone3-root-acceptance.json",
            *sorted((CHAMBERS / "reviews").glob("landmark3-*")),
        ]:
            if candidate.is_file():
                paths.add(candidate)
        for key in [
            "project_source_sha256",
            "configuration_sha256",
            "provider_active_source_sha256",
            "provider_original_source_sha256",
            "provider_import_patch_sha256",
            "verification_source_sha256",
        ]:
            paths.update(BASE / p for p in inventory[key])
        for cohort in ledger["accepted_cohorts"]:
            paths.update(
                BASE / f[k]
                for f in cohort["files"]
                for k in ["active_path", "original_path"]
            )
            paths.update(BASE / r["path"] for r in cohort["license_files"])
            paths.add(BASE / cohort["provenance"]["path"])
            for patch in cohort["patches"]:
                if "patch" in patch:
                    paths.add(BASE / patch["patch"]["path"])
                paths.update(BASE / p["path"] for p in patch.get("patch_files", []))
        for directory in [BASE, BASE / "landmarks", BASE / "ribbons", CHAMBERS]:
            paths.update(
                directory / p
                for p in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]
            )
        for binary in ["lean", "leanchecker", "lake"]:
            paths.add(
                Path(run("resolve-" + binary, [LAKE, "env", "which", binary]).strip())
            )
        first_before = snapshot(paths)
        record["preflight_source_inputs_sha256"] = first_before
        save()
        observer = [LAKE, "env", "lean", "../docs/provenance/ExportM3Dependencies.lean"]
        preliminary = output / "preliminary.raw.json"
        raw_paths.append(preliminary)
        run(
            "preliminary-observer",
            observer,
            {**os.environ, "GITHUB_PROOF_GRAPH_OUT": str(preliminary)},
        )
        require(
            snapshot(paths) == first_before,
            "Sources changed during preliminary observation",
        )
        preliminary_graph = read(preliminary)
        mods = {n["module"] for n in preliminary_graph["nodes"]}
        sources = {}
        source_paths = {}
        accepted = {
            f["module"]: (cohort, f)
            for cohort in ledger["accepted_cohorts"]
            for f in cohort["files"]
        }
        project_snapshot = {}
        for module in sorted(mods):
            source = None
            attribution = None
            if module in accepted:
                cohort, f = accepted[module]
                source = BASE / f["active_path"]
                attribution = {
                    "repository": cohort["repository"],
                    "revision": cohort["revision"],
                    "cohort": cohort["id"],
                    "active_source_path": f["active_path"],
                    "source_sha256": sha(source),
                    "upstream_path": f["upstream_path"],
                    "upstream_sha256": f["upstream_sha256"],
                    "status": "Accepted exact supplier cohort; active source may contain declared import/compatibility ports.",
                }
            else:
                relative = module.replace(".", "/") + ".lean"
                for family, directory in [
                    ("ArtinNormalisers", BASE),
                    ("ArtinTheorem18", BASE),
                    ("ArtinLandmarks", BASE / "landmarks"),
                    ("ArtinRibbons", BASE / "ribbons"),
                    ("ArtinChambers", CHAMBERS),
                ]:
                    if (
                        module == family
                        or module.startswith(family + ".")
                        or module == "ArtinNormalisersFull"
                    ) and (directory / relative).is_file():
                        source = directory / relative
                        repo_path = str(source.relative_to(BASE))
                        h = sha(source)
                        project_snapshot[repo_path] = h
                        committed = False
                        if repo_path in tree:
                            blob = subprocess.check_output(
                                ["git", "show", head + ":" + repo_path], cwd=BASE
                            )
                            committed = hashlib.sha256(blob).hexdigest() == h
                        attribution = {
                            "repository": "https://github.com/lazyinspirit/artin-tits-normalisers-lean",
                            "role": "locally authored project",
                            "source_path": repo_path,
                            "source_sha256": h,
                            "observed_base_git_head": head,
                            "exact_bytes_at_observed_head": committed,
                            "source_status": "committed exact source"
                            if committed
                            else "source snapshot uncommitted or changed against observed HEAD; exact SHA256 binding, not a Git blob claim",
                        }
                        if committed:
                            attribution["github_blob_url"] = (
                                "https://github.com/lazyinspirit/artin-tits-normalisers-lean/blob/"
                                + head
                                + "/"
                                + repo_path
                            )
                        break
                if source is None:
                    for directory, package in packages:
                        candidate = next(
                            (
                                p
                                for p in [
                                    directory / relative,
                                    directory / "src" / relative,
                                ]
                                if p.is_file()
                            ),
                            None,
                        )
                        if candidate:
                            source = candidate
                            attribution = {
                                "repository": package["url"].removesuffix(".git"),
                                "revision": package["rev"],
                                "source_path": str(source.relative_to(directory)),
                                "source_sha256": sha(source),
                                "role": "pinned foundation or transitive Lake dependency",
                            }
                            break
                if source is None and (prefix / "src/lean" / relative).is_file():
                    source = prefix / "src/lean" / relative
                    attribution = {
                        "repository": "https://github.com/leanprover/lean4",
                        "revision": "b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a",
                        "source_path": relative,
                        "source_sha256": sha(source),
                        "role": "bundled Lean foundation",
                    }
            require(
                source is not None and attribution is not None,
                "Unmapped defining module: " + module,
            )
            paths.add(source)
            sources[module] = attribution
            source_paths[module] = str(source.resolve())
        for item in preliminary_graph["artifact_paths"]:
            if item["module"] in mods:
                for p in item["object_paths"]:
                    paths.add(Path(p) if Path(p).is_absolute() else CHAMBERS / p)
        before = snapshot(paths)
        record["final_observer_inputs_sha256_before"] = before
        record["project_source_snapshot_sha256"] = project_snapshot
        save()
        final = output / "graph.raw.json"
        raw_paths.append(final)
        run(
            "final-observer",
            observer,
            {**os.environ, "GITHUB_PROOF_GRAPH_OUT": str(final)},
        )
        after = snapshot(paths)
        record["final_observer_inputs_sha256_after"] = after
        require(after == before, "Sources/objects changed during final observation")
        graph = read(final)
        require(
            graph == preliminary_graph,
            "Preliminary/final compiled declaration graphs differ",
        )
        current_physical = {
            r["module"]: sorted(r["names"])
            for r in graph["physical_project_modules"]
            if r["module"] == "ArtinChambers"
            or r["module"].startswith("ArtinChambers.")
        }
        require(
            current_physical == inventory["compiled_declaration_occurrences_by_module"],
            "M3 physical project names differ from frozen audited inventory",
        )
        baseline = json.loads(
            gzip.decompress((OUT / "dependency-graph.json.gz").read_bytes())
        )
        old_nodes = {n["name"]: n for n in baseline["nodes"]}
        new_nodes = {n["name"]: n for n in graph["nodes"]}
        require(
            set(baseline["roots"]) <= set(graph["roots"]),
            "An old project root was dropped",
        )
        for name, node in old_nodes.items():
            require(name in new_nodes, "Old reachable declaration absent: " + name)
            for key in [
                "kind",
                "has_value",
                "type_dependencies",
                "value_dependencies",
                "structural_dependencies",
            ]:
                require(
                    node[key] == new_nodes[name][key],
                    "Old declaration dependency content changed: " + name + ":" + key,
                )
        for node in graph["nodes"]:
            node["source"] = sources[node["module"]]
        graph["module_sources"] = sources
        graph["source_file_paths_at_observation"] = source_paths
        graph["scope"] = (
            "All project declarations through compiled M3, including physical private/generated declarations. This graph does not confer mathematical acceptance."
        )
        graph["physical_duplicate_limit"] = (
            "Canonical names appear once in the term graph. Exact project occurrence/alias rows are retained; old supplier occurrence audits remain separate accepted inventories."
        )
        graph["compiled_artifacts_sha256"] = {
            p: h for p, h in before.items() if ".olean" in Path(p).name
        }
        graph["project_source_snapshot_sha256"] = project_snapshot
        graph["observed_base_git_head"] = head
        annotated = output / "graph.json"
        annotated.write_text(
            json.dumps(graph, sort_keys=True, separators=(",", ":")) + "\n"
        )
        record["annotated_graph"] = compress(annotated)
        record["old_roots_and_dependency_edges_preserved"] = True
        record["counts"] = {
            "project_roots": len(graph["roots"]),
            "reachable_declarations": len(graph["nodes"]),
            "references": graph["edge_count"],
            "reachable_modules": len(mods),
            "physical_project_occurrences": graph["physical_project_occurrences"],
            "physical_project_aliases": len(
                graph["physical_project_identical_theorem_aliases"]
            ),
        }
        record["source_inventory_sha256"] = sha(inventory_path)
        record["technical_verification_sha256"] = sha(technical_path)
        record["inputs_unchanged"] = True
        record["baseline_sha256_after"] = {
            name: sha(OUT / name) for name in BASELINE_FILES
        }
        require(
            record["baseline_sha256_after"] == baseline_before,
            "A baseline archive input changed",
        )
        record["baseline_unchanged"] = True
        record["ok"] = True
    except BaseException as error:
        record["error"] = f"{type(error).__name__}: {error}"
    finally:
        record["raw_graphs"] = [compress(p) for p in raw_paths if p.is_file()]
        record["finished_at"] = utc()
        save()
    print(
        json.dumps(
            {
                "ok": record["ok"],
                "output": str(output),
                "counts": record.get("counts"),
                "error": record.get("error"),
            }
        )
    )
    return 0 if record["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
