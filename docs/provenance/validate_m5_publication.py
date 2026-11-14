#!/usr/bin/env python3
"""Validate publication bindings against preserved raw Git output; no Lean."""

from __future__ import annotations
import argparse, gzip, hashlib, io, json, subprocess
from pathlib import Path

BASE = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent


def sha(b):
    return hashlib.sha256(b).hexdigest()


def require(ok, msg):
    if not ok:
        raise RuntimeError(msg)


def raw(info):
    b = (BASE / info["path"]).read_bytes()
    require(sha(b) == info["compressed_sha256"], "Compressed Git evidence changed")
    plain = gzip.decompress(b)
    require(
        sha(plain) == info["uncompressed_sha256"]
        and len(plain) == info["uncompressed_bytes"],
        "Raw Git evidence changed",
    )
    return plain


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binding", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    path = args.binding.resolve()
    record = json.loads(path.read_text())
    output = (args.output or path.parent / "validation.json").resolve()
    require(not output.exists(), "Refuse to overwrite validation")
    require(
        record["ok"] is True
        and record["Lean_build_audit_or_kernel_replay_executed"] is False,
        "Publication record did not pass",
    )
    commit = record["commit"]
    resolved = subprocess.check_output(
        ["git", "rev-parse", "--verify", commit + "^{commit}"], cwd=BASE, text=True
    ).strip()
    require(resolved == commit, "Publication commit differs")
    tree_raw = raw(record["git_tree_raw_output"])
    actual_tree = subprocess.check_output(
        ["git", "ls-tree", "-rz", "--full-tree", commit], cwd=BASE
    )
    require(actual_tree == tree_raw, "Preserved tree differs from actual target commit")
    tree = {}
    for entry in tree_raw.split(b"\0"):
        if not entry:
            continue
        metadata, name = entry.split(b"\t", 1)
        mode, kind, oid = metadata.decode().split()
        tree[name.decode()] = (mode, kind, oid)
    batch = raw(record["git_cat_file_raw_output"])
    stdin = (BASE / record["git_cat_file_stdin"]["path"]).read_bytes()
    require(
        sha(stdin) == record["git_cat_file_stdin"]["sha256"], "Git batch input changed"
    )
    requested = stdin.decode().splitlines()
    stream = io.BytesIO(batch)
    blobs = {}
    for oid in requested:
        header = stream.readline().decode().strip().split()
        require(
            len(header) == 3 and header[:2] == [oid, "blob"], "Git blob header differs"
        )
        size = int(header[2])
        data = stream.read(size)
        require(
            len(data) == size and stream.read(1) == b"\n", "Truncated Git blob evidence"
        )
        object_bytes = b"blob " + str(size).encode() + b"\0" + data
        actual_oid = (
            hashlib.sha1(object_bytes)
            if len(oid) == 40
            else hashlib.sha256(object_bytes)
        ).hexdigest()
        require(actual_oid == oid, "Preserved payload does not have the Git object ID")
        blobs[oid] = (sha(data), size)
    require(stream.read() == b"", "Unexpected Git batch bytes")
    metadata = record.get("post_publication_observer_metadata", {})
    exact = record["exact_repository_source_bindings"]
    differences = record["non_scientific_historical_metadata_differences"]
    require(set(exact).isdisjoint(differences), "Duplicate binding dispositions")
    for source, row in {**exact, **differences}.items():
        require(
            source in tree
            and tree[source] == (row["git_mode"], "blob", row["git_blob_oid"]),
            "Path/blob identity differs: " + source,
        )
        digest, size = blobs[row["git_blob_oid"]]
        require(
            digest == row["git_blob_sha256"] and size == row["bytes"],
            "Published blob digest differs: " + source,
        )
        equal = row["snapshot_sha256"] == digest
        require(
            equal == row["snapshot_equals_published_blob"],
            "Snapshot comparison flag differs",
        )
        require(
            row["github_blob_url"]
            == "https://github.com/lazyinspirit/artin-tits-normalisers-lean/blob/"
            + commit
            + "/"
            + source,
            "Publication link differs",
        )
        require(
            equal if source in exact else not equal,
            "Source binding disposition differs",
        )
    require(
        set(differences) <= {"docs/provenance/GITHUB-PROOF-SOURCES.json"},
        "Unexplained mathematical/configuration/provider/review publication difference",
    )
    require(
        set(metadata)
        <= {
            "docs/provenance/ExportM5Dependencies.lean",
            "docs/provenance/run_m5_export.py",
        },
        "Unexpected post-publication observer metadata",
    )
    require(
        {
            "docs/provenance/ExportM5Dependencies.lean",
            "docs/provenance/run_m5_export.py",
        }
        <= set(exact) | set(metadata),
        "Observer inputs missing from publication accounting",
    )
    for source, row in metadata.items():
        require(
            source not in tree and source not in exact and source not in differences,
            "Post-publication source has a false Git blob classification",
        )
        preserved = BASE / row["preserved_copy"]["path"]
        require(
            sha(preserved.read_bytes())
            == row["snapshot_sha256"]
            == row["preserved_copy"]["sha256"],
            "Observer source copy changed",
        )
    inventory = json.loads((BASE / "asphericity/source-inventory.json").read_text())
    require(
        sha((BASE / "asphericity/source-inventory.json").read_bytes())
        == record["source_inventory_sha256"],
        "Frozen inventory changed",
    )
    for key in [
        "project_source_sha256",
        "configuration_sha256",
        "provider_active_source_sha256",
        "provider_original_source_sha256",
        "provider_import_patch_sha256",
        "verification_source_sha256",
        "provider_assembly_sha256",
        "provider_verification_source_sha256",
        "provider_statement_reviews_sha256",
        "provider_reused_source_sha256",
        "provider_evidence_sha256",
        "historical_reviews_sha256",
        "provider_statement_reviews_sha256",
    ]:
        for source, digest in inventory.get(key, {}).items():
            require(
                source in exact and exact[source]["snapshot_sha256"] == digest,
                "Frozen source missing or changed: " + source,
            )
    observation = json.loads(
        (BASE / record["compiled_observation"]["path"]).read_text()
    )
    require(
        sha((BASE / record["compiled_observation"]["path"]).read_bytes())
        == record["compiled_observation"]["sha256"],
        "Observation record changed",
    )
    for source, digest in observation["final_observer_inputs_sha256_before"].items():
        p = Path(source)
        if ".olean" in p.name or ".lake" in p.parts:
            continue
        try:
            relative = str(p.relative_to(BASE))
        except ValueError:
            continue
        require(
            relative in exact or relative in differences or relative in metadata,
            "Repository-owned observed snapshot missing: " + relative,
        )
        require(
            ({**exact, **differences, **metadata})[relative]["snapshot_sha256"]
            == digest,
            "Observed snapshot digest differs: " + relative,
        )
    for command in record["commands"]:
        require(command["exit_code"] == 0, "Recorded Git command failed")
    require(
        record["commands"][1]["stdout_sha256"] == sha(tree_raw)
        and record["commands"][2]["stdout_sha256"] == sha(batch),
        "Actual command output hashes differ",
    )
    baseline = {
        name: sha((OUT / name).read_bytes())
        for name in record["baseline_archive_sha256_before"]
    }
    require(
        baseline
        == record["baseline_archive_sha256_before"]
        == record["baseline_archive_sha256_after"],
        "Historical baseline archive changed",
    )
    result = {
        "kind": "publication-blob-integrity-validation",
        "ok": True,
        "commit": commit,
        "binding_sha256": sha(path.read_bytes()),
        "validator_sha256": sha(Path(__file__).read_bytes()),
        "exact_source_bindings": len(exact),
        "M5-prerequisites_project_source_files": len(
            inventory["project_source_sha256"]
        ),
        "allowed_historical_non_scientific_differences": list(differences),
        "all_repository_owned_observed_snapshots_accounted_for": True,
        "post_publication_observer_inputs_preserved_without_false_Git_links": list(
            metadata
        ),
        "actual_Git_tree_matches_preserved_output": True,
        "all_raw_blobs_match_Git_object_IDs": True,
        "all_frozen_source_config_provider_review_bindings_match": True,
        "baseline_archive_unchanged": True,
        "Lean_commands_executed": False,
        "clean_CI_result_asserted": False,
        "limits": "Validates exact source-publication and evidence integrity; clean CI and mathematical acceptance remain separate records.",
    }
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
