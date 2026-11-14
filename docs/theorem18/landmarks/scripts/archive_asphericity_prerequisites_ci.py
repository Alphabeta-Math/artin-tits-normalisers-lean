#!/usr/bin/env python3
"""Preserve and validate successful asphericity-prerequisites Actions evidence.

Adapted from archive_milestone4_ci.py. This archives prerequisites only;
actual asphericity, full landmark 5 and full Theorem 1.8 must remain unproved.
"""
import argparse
import ast
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile

BASE = Path(__file__).resolve().parents[4]
REPO = "lazyinspirit/artin-tits-normalisers-lean"
PACKAGE = "asphericity"
SCOPE_FALSE = (
    "full_landmark_5_proved",
    "actual_arrangement_asphericity_proved",
    "full_theorem_1_8_proved",
)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def aggregate(mapping):
    return sha(json.dumps(mapping, sort_keys=True, separators=(",", ":")).encode())


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def gh(*args):
    return subprocess.check_output(["gh", *args], cwd=BASE)


def review_keys():
    """Read the actual verifier's binding inventory without executing it."""
    tree = ast.parse((BASE / PACKAGE / "scripts/verify.py").read_text())
    values = [
        ast.literal_eval(node.value)
        for node in tree.body
        if isinstance(node, ast.Assign)
        and any(isinstance(t, ast.Name) and t.id == "REVIEW_KEYS" for t in node.targets)
    ]
    require(len(values) == 1 and isinstance(values[0], list), "Missing verifier REVIEW_KEYS")
    keys = values[0]
    require(all(isinstance(k, str) for k in keys) and len(keys) == len(set(keys)), "Malformed REVIEW_KEYS")
    require({"provider_reused_source_sha256", "provider_evidence_sha256"} <= set(keys),
            "Incomplete provider binding inventory")
    return keys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run_id", type=int)
    args = parser.parse_args()
    out = BASE / "docs/theorem18/landmarks/github-evidence" / f"run-{args.run_id}"
    # Refuse every existing directory, including any successful archive.
    out.mkdir(parents=True, exist_ok=False)

    def metadata(name, endpoint):
        raw = gh("api", endpoint)
        (out / name).write_bytes(raw)
        return json.loads(raw)

    run = metadata("run.json", f"/repos/{REPO}/actions/runs/{args.run_id}")
    require(run["status"] == "completed" and run["conclusion"] == "success", "Run not successful")
    require(run["path"] == ".github/workflows/asphericity.yml", "Wrong workflow")
    jobs = metadata("jobs.json", f"/repos/{REPO}/actions/runs/{args.run_id}/jobs?per_page=100")
    require(jobs["total_count"] == len(jobs["jobs"]) == 1
            and all(j["conclusion"] == "success" for j in jobs["jobs"]), "Wrong jobs")
    arts = metadata("artifacts.json", f"/repos/{REPO}/actions/runs/{args.run_id}/artifacts?per_page=100")
    require(arts["total_count"] == len(arts["artifacts"]), "Incomplete artifact metadata")
    selected = [a for a in arts["artifacts"] if a["name"] == "lean-asphericity-prerequisites-verification"]
    require(len(selected) == 1 and not selected[0]["expired"], "Artifact missing/ambiguous/expired")
    artifact = selected[0]
    archive_path = out / "asphericity-prerequisites-verification.zip"
    with archive_path.open("wb") as stream:
        subprocess.run(["gh", "api", f'/repos/{REPO}/actions/artifacts/{artifact["id"]}/zip'],
                       cwd=BASE, stdout=stream, check=True)
    digest = sha(archive_path.read_bytes())
    require(artifact["digest"] == "sha256:" + digest, "GitHub artifact digest differs")
    with gzip.GzipFile(filename=str(out / "actions.log.gz"), mode="wb", mtime=0) as stream:
        stream.write(gh("run", "view", str(args.run_id), "--repo", REPO, "--log"))

    checked_sources, ci_only_inputs = {}, {}
    with zipfile.ZipFile(archive_path) as archive:
        require(len(archive.namelist()) == len(set(archive.namelist())), "Duplicate ZIP members")

        def raw(path):
            return archive.read(path)

        def read(path):
            return json.loads(raw(path))

        result = read("verification.json")
        require(result["ok"] is True and result["inputs_unchanged"] is True
                and result["mode"] == "final" and result["semantic_acceptance_claimed"] is True
                and result["accepted_asphericity_prerequisites"] is True
                and all(result[k] is False for k in SCOPE_FALSE), "Wrong scope/result")
        require(result["kind"] == "source-bound-asphericity-prerequisites-verification", "Wrong verifier kind")
        require(result["repository_head"] == run["head_sha"], "Wrong source commit")
        commands = result["commands"]
        require(len(commands) == 67 and all(c["exit_code"] == 0 for c in commands), "Wrong/failed commands")
        for command in commands:
            require(sha(raw(command["log"])) == command["log_sha256"], "Changed command log")
        require(sha(raw("inputs.json")) == result["inputs_sha256"], "Input manifest changed")
        require(sha(raw("project-coverage.json")) == result["project_coverage_sha256"], "Coverage changed")
        inputs, coverage = read("inputs.json"), read("project-coverage.json")
        inv_path = BASE / PACKAGE / "source-inventory.json"
        inv = json.loads(inv_path.read_text())
        require(inv["accepted_asphericity_prerequisites"] is False
                and all(inv[k] is False for k in SCOPE_FALSE), "Candidate inventory overstates scope")
        for key in ("audited_declarations_by_module", "compiled_declaration_occurrences_by_module",
                    "compiled_duplicate_equivalences"):
            require(coverage[key] == inv[key], "Frozen inventory coverage differs: " + key)
        summary = coverage["summary"]
        require(summary == {
            "modules": 8, "canonical_project_declarations": 138, "physical_occurrences": 138,
            "distinct_physical_names": 138, "identical_theorem_duplicates": 0,
            "external_canonical_names": 0, "canonical_axioms_checked": True,
            "all_physical_type_value_universe_parameters_identical": True,
        }, "Wrong project declaration/physical coverage")
        require(len(result["accepted_context_input_sha256"]) == 996
                and result["unified_historical_source_context_count"] == 996
                and result["accepted_historical_input_counts"] == [996], "Wrong historical context")
        context_digest = aggregate(result["accepted_context_input_sha256"])
        require(result["accepted_context_input_aggregate_sha256"] == context_digest, "Changed historical digest")

        # Remap only this run's actual checkout/output. CI binaries and toolchain
        # files retain their recorded hashes; do not compare unrelated local builds.
        runner_base = Path(commands[0]["cwd"]).parent
        runner_output = runner_base / "asphericity/evidence/asphericity-prerequisites-ci"
        for absolute, expected in inputs["source_and_records_sha256"].items():
            path = Path(absolute)
            require(path.is_absolute(), "Nonabsolute bound runner input")
            if path.is_relative_to(runner_output):
                require(sha(raw(str(path.relative_to(runner_output)))) == expected, "Changed embedded replay source")
            elif path.is_relative_to(runner_base) and ".lake" not in path.relative_to(runner_base).parts:
                relative = path.relative_to(runner_base)
                require(sha((BASE / relative).read_bytes()) == expected, "Current source changed: " + str(relative))
                checked_sources[str(relative)] = expected
            else:
                ci_only_inputs[absolute] = expected
        require(len(inputs["source_and_records_sha256"]) == result["bound_input_count"], "Input count differs")
        for path, expected in inputs["compiled_parts_sha256"].items():
            require(inputs["source_and_records_sha256"].get(path) == expected, "Unbound CI compiled part")
        for key in ("accepted_context_input_sha256", "accepted_context_verification_sha256",
                    "historical_reviews_sha256", "provider_statement_reviews_sha256",
                    "project_statement_reviews_sha256"):
            for path, expected in result[key].items():
                require(checked_sources.get(path) == expected, "Unbound source/review: " + path)
        require(checked_sources.get("asphericity/source-inventory.json") == sha(inv_path.read_bytes()),
                "Final inventory not bound")

        bindings = dict(result["source_bindings"])
        bindings["accepted_context_input_aggregate_sha256"] = context_digest
        verification_paths = ("asphericity/ProjectAudit.lean", "asphericity/scripts/verify.py",
                              "asphericity/scripts/cache_prerequisites.py", ".github/workflows/asphericity.yml")
        bindings["verification_source_sha256"] = {p: sha((BASE / p).read_bytes()) for p in verification_paths}
        keys = review_keys()
        require(set(keys) == set(bindings), "Verifier REVIEW_KEYS/source bindings differ")
        for key in keys:
            require(bindings[key] == inv[key], "Frozen source inventory differs: " + key)
            if isinstance(bindings[key], dict):
                for path, expected in bindings[key].items():
                    require(checked_sources.get(path) == expected, "Unbound REVIEW_KEYS file: " + path)
        providers = json.loads((BASE / "asphericity/vendor/provenance.json").read_text())
        scalar_paths = {"vendor_provenance_sha256": "asphericity/vendor/provenance.json",
                        "provider_audit_sha256": "asphericity/ProviderAudit.lean",
                        "provider_license_sha256": "asphericity/vendor/" + providers["license"]["path"]}
        for key, path in scalar_paths.items():
            require(checked_sources.get(path) == bindings[key], "Unbound scalar provider input: " + key)

        project_counts = {m: len(names) for m, names in inv["compiled_declaration_occurrences_by_module"].items()}
        provider_coverage = json.loads((BASE / "asphericity/evidence/providers/coverage.json").read_text())
        provider_counts = {r["module"]: r["declarations"] for r in provider_coverage["physical_modules"]}
        require(len(project_counts) == 8 and sum(project_counts.values()) == 138, "Wrong project replay cohort")
        require(len(provider_counts) == len(providers["files"]) == 11 and sum(provider_counts.values()) == 310
                and set(provider_counts) == {r["module"] for r in providers["files"]}, "Wrong provider replay cohort")
        require(result["provider_physical_summary"] == provider_coverage["summary"]
                and provider_coverage["summary"]["canonical_axioms_checked"] is True
                and provider_coverage["summary"]["all_physical_type_value_universe_parameters_identical"] is True
                and provider_coverage["summary"]["identical_theorem_duplicates"] == 0,
                "Provider canonical/physical coverage differs")
        counts = {**project_counts, **provider_counts}
        replays = result["exact_replays"]
        require(len(counts) == len(replays) == 19 and {r["module"] for r in replays} == set(counts),
                "Replay coverage differs")
        for row in replays:
            r = row["result"]
            require(r["module"] == row["module"] and r["exact"] is True and r["kernel_replay_passed"] is True
                    and r["declarations"] == row["physical_declarations_expected"] == counts[row["module"]],
                    "Replay result/count differs")
        for label in ("a", "b"):
            path = BASE / f"asphericity/reviews/asphericity-prerequisites-{label}.json"
            review = json.loads(path.read_text())
            require(review["verdict"] == "accept-asphericity-prerequisites" and review["model"] == "gpt-6.1-sol"
                    and review["reasoning_effort"] == "high" and review["accepted_asphericity_prerequisites"] is True
                    and all(review[k] is False for k in SCOPE_FALSE)
                    and review["source_inventory_sha256"] == checked_sources["asphericity/source-inventory.json"],
                    "Wrong independent prerequisite review")
            for key in keys:
                require(review[key] == bindings[key], "Stale independent review: " + label + ":" + key)
            (out / f"review-{label}.json").write_bytes(path.read_bytes())
            (out / f"review-{label}.md").write_bytes(path.with_suffix(".md").read_bytes())
        (out / "source-inventory.json").write_bytes(inv_path.read_bytes())
        (out / "verification.json").write_bytes(raw("verification.json"))
        report = {"ok": True, "run_id": args.run_id, "run_url": run["html_url"], "source_commit": run["head_sha"],
                  "accepted_asphericity_prerequisites": True, **{k: False for k in SCOPE_FALSE},
                  "artifact_sha256": digest, "github_artifact_digest_matches": True,
                  "current_source_input_count": len(checked_sources), "historical_input_count": 996,
                  "independent_review_count": 2, "project_summary": summary,
                  "project_exact_replays": 8, "provider_exact_replays": 11, "provider_declarations": 310,
                  "checked_raw_log_count": len(commands), "review_binding_keys": keys,
                  "checked_source_sha256": checked_sources, "ci_only_input_count": len(ci_only_inputs),
                  "limitations": ["Prerequisites only: actual arrangement asphericity, full M5 and Theorem 1.8 remain unproved.",
                      "CI compiled/toolchain hashes recorded, not compared to unrelated local binaries.",
                      "Bundled kernel relative to imported environments; old accepted suppliers and Mathlib not freshly replayed."]}
        (out / "archive-verification.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    (out / "README.md").write_text(
        "# Asphericity prerequisites: fresh CI and permanent proof records\n\n"
        "Actual finite/central/basis-simplicial geometry, finite convex good cover, genuine universal-cover/local topology, "
        "and generic directed-cover criterion. Actual arrangement asphericity, full landmark 5 and Theorem 1.8 remain unproved.\n\n"
        f'- Run: <{run["html_url"]}>\n- Source commit: `{run["head_sha"]}`.\n'
        "- Eight project and eleven new supplier exact-module replays passed.\n"
        "- Both independent source-bound prerequisite reviews, every REVIEW_KEYS binding and 996 unchanged historical inputs checked.\n"
        "- Original artifact ZIP, complete compressed Actions log, metadata, final inventory and reviews are retained.\n\n"
        "See archive-verification.json for exact declaration counts, source/log hashes and verification limits.\n")
    (out / "SHA256SUMS").write_text("".join(sha(p.read_bytes()) + "  " + p.name + "\n"
        for p in sorted(out.iterdir()) if p.name != "SHA256SUMS"))
    print(json.dumps({k: v for k, v in report.items() if k != "checked_source_sha256"}, indent=2))


if __name__ == "__main__":
    main()
