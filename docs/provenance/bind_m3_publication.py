#!/usr/bin/env python3
"""Bind source snapshots to an immutable published Git commit, without Lean.

Every repository-owned snapshot source/record is compared to the actual Git blob.
Frozen mathematical/provider/configuration/review sources must match. A mutable
pre-export registry snapshot may differ and is explicitly retained as historical
metadata. External foundations and compiled objects are never mislabeled as Git
blobs in this project. Raw Git batch output and command evidence are retained.
"""

from __future__ import annotations
import argparse, datetime as dt, gzip, hashlib, io, json, subprocess, time
from pathlib import Path

BASE = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


def sha(p):
    return sha_bytes(Path(p).read_bytes())


def read(p):
    return json.loads(Path(p).read_text())


def require(test, msg):
    if not test:
        raise RuntimeError(msg)


def pack(path, data):
    with gzip.GzipFile(filename=str(path), mode="wb", mtime=0) as f:
        f.write(data)
    return {
        "path": str(path.relative_to(BASE)),
        "compressed_sha256": sha(path),
        "uncompressed_sha256": sha_bytes(data),
        "uncompressed_bytes": len(data),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--run", type=Path, default=OUT / "m3/run-20261114T065009Z")
    parser.add_argument("--ci-run", required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    run = args.run.resolve()
    execution = read(run / "execution.json")
    inventory = read(BASE / "chambers/source-inventory.json")
    acceptance_path = BASE / "docs/theorem18/landmarks/milestone3-root-acceptance.json"
    acceptance = read(acceptance_path)
    require(
        execution["ok"] and execution["baseline_unchanged"],
        "Compiled observation did not pass",
    )
    output = (args.output or OUT / "publications" / args.commit).resolve()
    output.mkdir(parents=True, exist_ok=False)
    baseline_before = {
        name: sha(OUT / name) for name in execution["baseline_sha256_before"]
    }
    commands = []

    def run_git(label, argv, input_bytes=None):
        t = time.monotonic()
        result = subprocess.run(
            argv,
            cwd=BASE,
            input=input_bytes,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        row = {
            "argv": argv,
            "cwd": "repository root",
            "exit_code": result.returncode,
            "elapsed_seconds": round(time.monotonic() - t, 6),
            "stdout_sha256": sha_bytes(result.stdout),
            "stderr": result.stderr.decode(errors="replace"),
        }
        if input_bytes is not None:
            row["stdin_sha256"] = sha_bytes(input_bytes)
        commands.append(row)
        require(result.returncode == 0, label + " failed: " + row["stderr"])
        return result.stdout

    commit = (
        run_git(
            "resolve commit",
            ["git", "rev-parse", "--verify", args.commit + "^{commit}"],
        )
        .decode()
        .strip()
    )
    require(commit == args.commit, "Use the full immutable commit SHA")
    tree_raw = run_git(
        "read complete Git tree", ["git", "ls-tree", "-rz", "--full-tree", commit]
    )
    tree = {}
    for row in tree_raw.split(b"\0"):
        if not row:
            continue
        metadata, path = row.split(b"\t", 1)
        mode, kind, oid = metadata.decode().split()
        tree[path.decode()] = {"mode": mode, "kind": kind, "git_blob_oid": oid}
    tree_record = pack(output / "git-ls-tree.stdout.gz", tree_raw)
    expected = {}
    roles = {}
    bases = {}
    source_inputs = execution["final_observer_inputs_sha256_before"]
    external = []
    artifacts = []

    def bind(path, digest, role, basis):
        require(len(digest) == 64, "Invalid snapshot digest: " + path)
        require(
            path not in expected or expected[path] == digest,
            "Conflicting snapshot source hashes: " + path,
        )
        expected[path] = digest
        roles.setdefault(path, []).append(role)
        bases.setdefault(path, []).append(basis)

    for absolute, digest in source_inputs.items():
        path = Path(absolute)
        if ".olean" in path.name:
            artifacts.append({"observed_path": absolute, "sha256": digest})
            continue
        try:
            relative = str(path.relative_to(BASE))
        except ValueError:
            external.append(
                {
                    "observed_path": absolute,
                    "sha256": digest,
                    "publication_scope": "external pinned source/toolchain, not a project Git blob",
                }
            )
            continue
        if ".lake" in path.parts:
            external.append(
                {
                    "observed_path": absolute,
                    "sha256": digest,
                    "publication_scope": "Lake/toolchain prerequisite, not a tracked project Git blob",
                }
            )
            continue
        bind(
            relative,
            digest,
            "M3 observer source/record snapshot",
            "exact observed snapshot before/after the final observer",
        )
    technical_path = Path(execution["technical_record"])
    technical = read(technical_path)
    for path, digest in technical["accepted_context_input_sha256"].items():
        bind(
            path,
            digest,
            "unchanged accepted context",
            "archived855-input accepted-context union",
        )
    for key in [
        "project_source_sha256",
        "configuration_sha256",
        "provider_active_source_sha256",
        "provider_original_source_sha256",
        "provider_import_patch_sha256",
        "verification_source_sha256",
        "historical_reviews_sha256",
        "provider_statement_reviews_sha256",
    ]:
        for path, digest in inventory.get(key, {}).items():
            bind(path, digest, key, "frozen M3 source inventory")
    for path, digest in acceptance["independent_reviews_sha256"].items():
        bind(
            path,
            digest,
            "accepted independent final M3 review",
            "root mathematical acceptance receipt",
        )
    bind(
        "chambers/source-inventory.json",
        execution["source_inventory_sha256"],
        "frozen source inventory",
        "M3 compiled observation",
    )
    bind(
        str(technical_path.relative_to(BASE)),
        execution["technical_verification_sha256"],
        "source-bound technical verification",
        "M3 compiled observation",
    )
    # Earlier accepted review receipts are included even where the older source
    # input manifests did not themselves contain their own review files.
    for directory in [
        "docs/reviews",
        "docs/full/reviews",
        "docs/theorem18/reviews",
        "landmarks/reviews",
        "ribbons/reviews",
        "chambers/reviews",
    ]:
        for path in sorted((BASE / directory).glob("*")):
            if path.is_file() and path.suffix in [".json", ".md"]:
                relative = str(path.relative_to(BASE))
                if relative in expected:
                    roles[relative].append(
                        "retained review or source-correspondence record"
                    )
                else:
                    bind(
                        relative,
                        sha(path),
                        "retained review/source-correspondence record",
                        "additional current retained record; no new mathematical acceptance inferred",
                    )
    missing = [p for p in expected if p not in tree]
    require(not missing, "Source/record absent from target commit: " + str(missing))
    blob_ids = sorted({tree[p]["git_blob_oid"] for p in expected})
    stdin = ("\n".join(blob_ids) + "\n").encode()
    (output / "git-cat-file.stdin.txt").write_bytes(stdin)
    batch = run_git("read exact Git blobs", ["git", "cat-file", "--batch"], stdin)
    batch_record = pack(output / "git-cat-file.stdout.gz", batch)
    stream = io.BytesIO(batch)
    blobs = {}
    for requested in blob_ids:
        header = stream.readline().decode().rstrip("\n").split()
        require(
            len(header) == 3 and header[0] == requested and header[1] == "blob",
            "Unexpected Git batch header",
        )
        size = int(header[2])
        data = stream.read(size)
        require(
            len(data) == size and stream.read(1) == b"\n", "Truncated Git batch payload"
        )
        blobs[requested] = {"sha256": sha_bytes(data), "bytes": size}
    require(stream.read() == b"", "Unexpected trailing Git batch output")
    bindings = {}
    differences = {}
    for path, digest in sorted(expected.items()):
        entry = tree[path]
        blob = blobs[entry["git_blob_oid"]]
        same = blob["sha256"] == digest
        row = {
            "snapshot_sha256": digest,
            "git_blob_oid": entry["git_blob_oid"],
            "git_blob_sha256": blob["sha256"],
            "git_mode": entry["mode"],
            "bytes": blob["bytes"],
            "snapshot_equals_published_blob": same,
            "roles": sorted(set(roles[path])),
            "binding_basis": sorted(set(bases[path])),
            "github_blob_url": "https://github.com/lazyinspirit/artin-tits-normalisers-lean/blob/"
            + commit
            + "/"
            + path,
        }
        if same:
            bindings[path] = row
        else:
            require(
                path == "docs/provenance/GITHUB-PROOF-SOURCES.json",
                "Frozen scientific/configuration/review source differs from publication: "
                + path,
            )
            row["disposition"] = (
                "Historical mutable registry metadata snapshot differs from its completed publication version; no proof/configuration/provider/review bytes differ. Original observer snapshot remains unchanged."
            )
            differences[path] = row
    for path in inventory["project_source_sha256"]:
        require(path in bindings, "M3 scientific source not exactly bound: " + path)
    baseline_after = {name: sha(OUT / name) for name in baseline_before}
    require(baseline_before == baseline_after, "Baseline archive changed")
    result = {
        "kind": "immutable-M3-source-publication-binding",
        "ok": True,
        "commit": commit,
        "repository": "https://github.com/lazyinspirit/artin-tits-normalisers-lean",
        "compiled_observation": {
            "path": str((run / "execution.json").relative_to(BASE)),
            "sha256": sha(run / "execution.json"),
            "observed_base_git_head": execution["observed_git_head"],
            "precommit_observation_preserved": True,
        },
        "source_inventory_sha256": sha(BASE / "chambers/source-inventory.json"),
        "root_acceptance_sha256": sha(acceptance_path),
        "commands": commands,
        "git_tree_raw_output": tree_record,
        "git_cat_file_raw_output": batch_record,
        "git_cat_file_stdin": {
            "path": str((output / "git-cat-file.stdin.txt").relative_to(BASE)),
            "sha256": sha(output / "git-cat-file.stdin.txt"),
        },
        "exact_repository_source_bindings": bindings,
        "non_scientific_historical_metadata_differences": differences,
        "external_source_snapshots": external,
        "compiled_artifact_snapshots_not_git_sources": artifacts,
        "baseline_archive_sha256_before": baseline_before,
        "baseline_archive_sha256_after": baseline_after,
        "M3_project_source_count": len(inventory["project_source_sha256"]),
        "exact_source_binding_count": len(bindings),
        "semantic_acceptance": "Separate root receipt and both independent final statement reviews; publication binding adds no mathematics.",
        "clean_github_ci": {
            "url": args.ci_run,
            "status": "pending/in progress (root supplied); no successful CI result asserted",
        },
        "Lean_build_audit_or_kernel_replay_executed": False,
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "binding_script_sha256": sha(Path(__file__)),
        "limits": [
            "Source/configuration/provider/review hashes bound to actual Git blob bytes at the exact commit.",
            "External foundations are pinned to their own repositories/toolchain records and are not claimed as blobs in this project commit.",
            "Original precommit graph/source-attribution observations, raw exports and execution records were not rewritten.",
        ],
    }
    (output / "binding.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n"
    )
    print(
        json.dumps(
            {
                "ok": True,
                "output": str(output / "binding.json"),
                "exact_bindings": len(bindings),
                "historical_non_scientific_differences": len(differences),
                "M3_project_sources": len(inventory["project_source_sha256"]),
                "commit": commit,
                "CI": "pending",
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
