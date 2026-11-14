#!/usr/bin/env python3
"""Archive a successful full-Theorem-1.8 manual CI run bound to its exact commit.

This does not dispatch a workflow, push, or publish. Run after final CI as:
  python3 docs/theorem18/landmarks/scripts/archive_deligne_ci.py RUN_ID \
      --source-commit FULL_40_CHARACTER_SCIENCE_COMMIT
The new permanent archive contains the original Actions artifact, compressed
complete run log, a deterministic Git source archive, metadata and checked
review/inventory records. Existing archives are never overwritten.
"""

import argparse
import ast
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import zipfile

BASE = Path(__file__).resolve().parents[4]
REPO = "lazyinspirit/artin-tits-normalisers-lean"
PACKAGE = "deligne"
WORKFLOW = ".github/workflows/deligne.yml"
ARTIFACT = "lean-deligne-theorem18-verification"
OUTPUT = "deligne/evidence/theorem18-ci"
# Inspected Lean 4.36.0-rc2 LeanChecker.replayFromImports, including its
# exported/server/private loading and kernel replay; CLI prefix selection is
# deliberately not used. The earlier development helper SHA6e6c76359e6f3999...
# required that CLI and is retained in truthful failed-observation bindings.
OFFICIAL_CHECKER_SOURCE_SHA256 = "4a406b8ed95da0377206600b7b00a03bedc05102c0fadad641ffe0bfdb95122f"
SCOPE_TRUE = (
    "full_landmark_5_proved",
    "actual_arrangement_asphericity_proved",
    "full_theorem_1_8_proved",
)
SCOPE_FALSE = (
    "two_sided_nerve_homotopy_equivalence_proved",
    "actual_universal_cover_contractible_proved",
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


def committed(commit, path):
    relative = PurePosixPath(path)
    require(not relative.is_absolute() and ".." not in relative.parts, "Unsafe source path")
    return subprocess.check_output(["git", "show", f"{commit}:{relative}"], cwd=BASE)


def review_keys(commit):
    tree = ast.parse(committed(commit, "deligne/scripts/verify.py"))
    values = [ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
              and any(isinstance(t, ast.Name) and t.id == "REVIEW_KEYS" for t in n.targets)]
    require(len(values) == 1 and isinstance(values[0], list), "Missing verifier REVIEW_KEYS")
    keys = values[0]
    require(all(isinstance(k, str) for k in keys) and len(keys) == len(set(keys)),
            "Malformed verifier REVIEW_KEYS")
    return keys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run_id", type=int)
    parser.add_argument("--source-commit", required=True,
                        help="Exact reviewed science commit, all 40 lowercase hex characters")
    args = parser.parse_args()
    require(re.fullmatch(r"[0-9a-f]{40}", args.source_commit) is not None,
            "A full immutable source commit is required")
    commit = args.source_commit
    require(subprocess.check_output(["git", "cat-file", "-t", commit], cwd=BASE).strip()
            == b"commit", "Source object is not a locally available commit")
    out = BASE / "docs/theorem18/landmarks/github-evidence" / f"run-{args.run_id}"
    out.mkdir(parents=True, exist_ok=False)

    def metadata(name, endpoint):
        raw = gh("api", endpoint)
        (out / name).write_bytes(raw)
        return json.loads(raw)

    run = metadata("run.json", f"/repos/{REPO}/actions/runs/{args.run_id}")
    require(run["status"] == "completed" and run["conclusion"] == "success", "Run not successful")
    require(run["path"] == WORKFLOW and run["event"] == "workflow_dispatch", "Wrong workflow/event")
    require(run["head_sha"] == commit, "Run does not certify the requested science commit")
    remote_commit = metadata("source-commit.json", f"/repos/{REPO}/commits/{commit}")
    require(remote_commit["sha"] == commit, "Remote science commit differs")
    jobs = metadata("jobs.json", f"/repos/{REPO}/actions/runs/{args.run_id}/jobs?per_page=100")
    require(jobs["total_count"] == len(jobs["jobs"]) == 1
            and all(j["conclusion"] == "success" for j in jobs["jobs"]), "Wrong/failed jobs")
    arts = metadata("artifacts.json", f"/repos/{REPO}/actions/runs/{args.run_id}/artifacts?per_page=100")
    require(arts["total_count"] == len(arts["artifacts"]), "Incomplete artifact metadata")
    selected = [a for a in arts["artifacts"] if a["name"] == ARTIFACT]
    require(len(selected) == 1 and not selected[0]["expired"], "Artifact missing/ambiguous/expired")
    artifact = selected[0]
    require(artifact["workflow_run"]["id"] == args.run_id
            and artifact["workflow_run"]["head_sha"] == commit, "Artifact run/source differs")
    archive_path = out / "deligne-theorem18-verification.zip"
    with archive_path.open("wb") as stream:
        subprocess.run(["gh", "api", f"/repos/{REPO}/actions/artifacts/{artifact['id']}/zip"],
                       cwd=BASE, stdout=stream, check=True)
    digest = sha(archive_path.read_bytes())
    require(artifact["digest"] == "sha256:" + digest, "GitHub artifact digest differs")
    with gzip.GzipFile(filename=str(out / "actions.log.gz"), mode="wb", mtime=0) as stream:
        stream.write(gh("run", "view", str(args.run_id), "--repo", REPO, "--log"))
    # Git archive expands the exact immutable tree; gzip time/name are fixed.
    source_tar = subprocess.check_output(["git", "archive", "--format=tar", commit], cwd=BASE)
    require(subprocess.check_output(["git", "get-tar-commit-id"], input=source_tar, cwd=BASE)
            .decode().strip() == commit, "Source tar commit marker differs")
    with (out / "source.tar.gz").open("wb") as raw_stream:
        with gzip.GzipFile(filename="", fileobj=raw_stream, mode="wb", mtime=0) as stream:
            stream.write(source_tar)

    checked_sources, ci_only_inputs = {}, {}
    with zipfile.ZipFile(archive_path) as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)), "Duplicate ZIP members")
        require(all(not PurePosixPath(n).is_absolute() and ".." not in PurePosixPath(n).parts
                    for n in names), "Unsafe ZIP member")

        def raw(path):
            return archive.read(path)

        def read(path):
            return json.loads(raw(path))

        result = read("verification.json")
        require(result["ok"] is True and result["inputs_unchanged"] is True
                and result["mode"] == "final" and result["semantic_acceptance_claimed"] is True,
                "Verification is not a successful reviewed final run")
        require(all(result[k] is True for k in SCOPE_TRUE)
                and all(result[k] is False for k in SCOPE_FALSE), "Wrong theorem scope")
        require(result["kind"] == "source-bound-theorem18-verification", "Wrong verifier kind")
        require(result["repository_head"] == commit, "Verifier science commit differs")
        require(result["clean_skipped"] is False and result.get("clean_skip_reason") is None,
                "Final CI skipped cleaning")
        commands = result["commands"]
        require(commands and all(c["exit_code"] == 0 for c in commands), "Missing/failed commands")
        clean = [c for c in commands if c["label"] == "clean-new-package"]
        require(len(clean) == 1 and clean[0]["argv"] == ["lake", "clean", "artin-deligne"],
                "Missing actual final clean of this package")
        for c in commands:
            require(sha(raw(c["log"])) == c["log_sha256"], "Changed command log")
        require(sha(raw("inputs.json")) == result["inputs_sha256"], "Input manifest changed")
        inputs, coverage = read("inputs.json"), read("coverage.json")
        require(sha(raw("coverage.json")) == result["coverage_sha256"], "Coverage changed")
        inv_path = "deligne/source-inventory.json"
        inv_raw = committed(commit, inv_path)
        inv = json.loads(inv_raw)
        for key in ("audited_declarations_by_module", "compiled_declaration_occurrences_by_module",
                    "compiled_duplicate_equivalences", "external_canonical_declarations"):
            require(coverage[key] == inv[key], "Inventory coverage differs: " + key)
        summary = coverage["summary"]
        physical = coverage["compiled_declaration_occurrences_by_module"]
        canonical = coverage["audited_declarations_by_module"]
        require(summary["canonical_axioms_checked"] is True
                and summary["all_physical_type_value_universe_parameters_identical"] is True
                and summary["modules"] == len(physical)
                and summary["physical_occurrences"] == sum(len(v) for v in physical.values())
                and summary["canonical_project_declarations"] == sum(len(v) for v in canonical.values()),
                "Incomplete actual canonical/physical declaration audit")
        require("ArtinDeligne" in physical and physical["ArtinDeligne"] == []
                and all(bool(ns) for m, ns in physical.items() if m != "ArtinDeligne"),
                "Empty scientific module or non-import-only aggregate")
        require(inv["critical_declarations"], "No final critical theorem statements inventoried")
        require(inv["scope_claims"] == {**{k: True for k in SCOPE_TRUE},
                **{k: False for k in SCOPE_FALSE}}, "Wrong inventory theorem scope")
        context = result["accepted_context_input_sha256"]
        require(len(context) == result["accepted_context_input_count"] == 1264, "Wrong historical context")
        context_digest = aggregate(context)
        require(result["accepted_context_input_aggregate_sha256"] == context_digest,
                "Historical context digest differs")
        runner_base = Path(commands[0]["cwd"]).parent
        runner_output = runner_base / OUTPUT
        for absolute, expected in inputs["source_and_records_sha256"].items():
            path = Path(absolute)
            require(path.is_absolute(), "Nonabsolute bound runner input")
            if path.is_relative_to(runner_output):
                require(sha(raw(str(path.relative_to(runner_output)))) == expected,
                        "Changed embedded verification source")
            elif path.is_relative_to(runner_base) and ".lake" not in path.relative_to(runner_base).parts:
                relative = str(path.relative_to(runner_base))
                require(sha(committed(commit, relative)) == expected, "Changed committed input: " + relative)
                checked_sources[relative] = expected
            else:
                ci_only_inputs[absolute] = expected
        require(len(inputs["source_and_records_sha256"]) == result["bound_input_count"],
                "Input count differs")
        for path, expected in inputs["compiled_parts_sha256"].items():
            require(inputs["source_and_records_sha256"].get(path) == expected, "Unbound compiled part")
        for key in ("accepted_context_input_sha256", "accepted_context_verification_sha256",
                    "project_statement_reviews_sha256"):
            for path, expected in result[key].items():
                require(checked_sources.get(path) == expected, "Unbound source/review: " + path)
        require(checked_sources.get(inv_path) == sha(inv_raw), "Final source inventory not bound")
        keys = review_keys(commit)
        bindings = result["source_bindings"]
        require(set(keys) == set(bindings), "REVIEW_KEYS/source bindings differ")
        for key in keys:
            require(bindings[key] == inv[key], "Frozen source inventory differs: " + key)
            if isinstance(bindings[key], dict):
                for path, expected in bindings[key].items():
                    require(checked_sources.get(path) == expected, "Unbound reviewed input: " + path)
        require(bindings["accepted_context_input_aggregate_sha256"] == context_digest,
                "Review context digest differs")
        for required in (WORKFLOW, "deligne/scripts/verify.py", "deligne/ProjectAudit.lean",
                         "deligne/scripts/cache_prerequisites.py",
                         "docs/theorem18/landmarks/scripts/archive_deligne_ci.py"):
            require(checked_sources.get(required) == sha(committed(commit, required)),
                    "Verification source not bound: " + required)

        # Exact-module replay coverage is checked against physical project names
        # and every selected provider module, independently of command labels.
        project_counts = {m: len(physical[m]) for m in inv["project_modules"]}
        provider_counts = {}
        for cohort in ("weights", "carriers"):
            provenance = json.loads(committed(commit, f"deligne/vendor/provenance-{cohort}.json"))
            for row in provenance["files"]:
                module = row["module"]
                require(module not in provider_counts, "Duplicate provider module")
                provider_counts[module] = len(physical[module])
        modules = set(project_counts) | set(provider_counts)
        require(not set(project_counts) & set(provider_counts) and len(provider_counts) == 28,
                "Wrong selected provider cohort")
        require(set(result["project_modules"]) == set(project_counts)
                and set(result["new_provider_modules"]) == set(provider_counts), "Module inventory differs")
        replays = result["exact_replays"]
        require(len(replays) == len(modules) and {r["module"] for r in replays} == modules,
                "Exact replay module coverage differs")
        counts = {**project_counts, **provider_counts}
        commands_by_label = {c["label"]: c for c in commands}
        require(len(commands_by_label) == len(commands), "Duplicate command labels")
        # Re-extract the reviewed literal without executing a historical script.
        accepted_runner_path = "ribbons/scripts/verify_project.py"
        accepted_runner_raw = committed(commit, accepted_runner_path)
        require(context.get(accepted_runner_path) == sha(accepted_runner_raw),
                "Exact runner source is not in the accepted historical context")
        tree = ast.parse(accepted_runner_raw)
        literals = [ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
                    and any(isinstance(t, ast.Name) and t.id == "EXACT_REPLAY" for t in n.targets)]
        require(len(literals) == 1 and isinstance(literals[0], str), "Missing accepted exact runner")
        runner_raw = raw("ExactReplay.lean")
        runner_path = str(runner_output / "ExactReplay.lean")
        require(runner_raw == literals[0].encode()
                and result["exact_replay_runner"] == "ExactReplay.lean"
                and sha(runner_raw) == result["exact_replay_source_sha256"]
                == inputs["source_and_records_sha256"].get(runner_path),
                "Exact runner bytes/digest/embedded binding differ")
        checker_source = result["official_checker_source_path"]
        toolchain = raw(commands_by_label["toolchain-prefix"]["log"]).decode().strip()
        require(checker_source == str(Path(toolchain) / "src/lean/LeanChecker.lean")
                and result["official_checker_source_sha256"] == OFFICIAL_CHECKER_SOURCE_SHA256
                == inputs["source_and_records_sha256"].get(checker_source),
                "Pinned official replay algorithm source is not bound")
        for tool in ("lean", "lake", "leanchecker"):
            binary = raw(commands_by_label["resolve-" + tool]["log"]).decode().strip()
            require(Path(binary).is_absolute() and binary in inputs["source_and_records_sha256"],
                    "Replay tool binary is not bound: " + tool)
        replay_commands = [c for c in commands if c["argv"][:4] == ["lake", "env", "lean", "--run"]]
        require(len(replay_commands) == len(modules)
                and {c["argv"][5] for c in replay_commands if len(c["argv"]) == 6} == modules,
                "Missing fresh processes for exact-module replay")
        for row in replays:
            module = row["module"]
            require(row["official_kernel_replay"] is True and row["official_algorithm"] is True
                    and row["physical_declarations_expected"] == counts[module],
                    "Replay physical count/algorithm evidence differs")
            command = commands_by_label[row["command_label"]]
            require(command["argv"] == ["lake", "env", "lean", "--run", runner_path, module],
                    "Exact runner command/module differs")
            prefix = "EXACT_REPLAY_JSON "
            rows = [json.loads(line[len(prefix):]) for line in raw(command["log"]).decode().splitlines()
                    if line.startswith(prefix)]
            require(len(rows) == 1 and rows[0] == row["result"]
                    and rows[0]["module"] == module and rows[0]["exact"] is True
                    and rows[0]["kernel_replay_passed"] is True
                    and rows[0]["declarations"] == counts[module],
                    "Exact-module replay JSON/count/result differs")
        require(set(physical) == modules and set(canonical) == modules,
                "Audit has missing/extra exact modules")
        for label, argv in (
            ("build-exact-frontier", ["lake", "build", *result["project_modules"], *result["new_provider_modules"]]),
            ("project-statements-axioms-physical", ["lake", "env", "lean", "ProjectAudit.lean"]),
            ("literal-theorem-endpoints", ["lake", "env", "lean", "StatementAudit.lean"]),
        ):
            require(commands_by_label[label]["argv"] == argv, "Missing actual build/audit: " + label)
        audit = raw(commands_by_label["project-statements-axioms-physical"]["log"]).decode()
        def audit_rows(prefix):
            return [json.loads(line[len(prefix):]) for line in audit.splitlines() if line.startswith(prefix)]
        decls = audit_rows("DELIGNE_PROJECT_DECL_JSON ")
        require(decls and all(set(r["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
                             for r in decls), "Raw audit has forbidden axioms")
        require({m: sorted(r["name"] for r in decls if r["module"] == m) for m in modules}
                == canonical, "Raw declaration audit differs from coverage")
        physical_rows = audit_rows("DELIGNE_PROJECT_COMPILED_MODULE_JSON ")
        require(len(physical_rows) == len(modules)
                and {r["module"]: sorted(r["names"]) for r in physical_rows} == physical,
                "Raw physical audit differs from coverage")
        require(audit_rows("DELIGNE_PROJECT_SUMMARY_JSON ") == [summary], "Raw audit summary differs")
        for label in ("a", "b"):
            path = f"deligne/reviews/theorem18-{label}.json"
            review_raw = committed(commit, path)
            review = json.loads(review_raw)
            require(review["verdict"] == "accept-theorem-1-8"
                    and review["model"] == "gpt-6.1-sol" and review["reasoning_effort"] == "high"
                    and all(review[k] is True for k in SCOPE_TRUE)
                    and all(review[k] is False for k in SCOPE_FALSE)
                    and review["source_inventory_sha256"] == sha(inv_raw), "Wrong/stale main review")
            for key in keys:
                require(review[key] == bindings[key], "Stale main review: " + label + ":" + key)
            for key in ("critical_declarations", "audited_declarations_by_module",
                        "compiled_declaration_occurrences_by_module", "compiled_duplicate_equivalences",
                        "external_canonical_declarations"):
                require(review[key] == inv[key], "Stale review declaration inventory: " + key)
            (out / f"review-{label}.json").write_bytes(review_raw)
            (out / f"review-{label}.md").write_bytes(committed(commit, path[:-5] + ".md"))
        (out / "source-inventory.json").write_bytes(inv_raw)
        (out / "verification.json").write_bytes(raw("verification.json"))
        (out / "coverage.json").write_bytes(raw("coverage.json"))
        report = {
            "ok": True, "run_id": args.run_id, "run_url": run["html_url"],
            "source_commit": commit, **{k: True for k in SCOPE_TRUE}, **{k: False for k in SCOPE_FALSE},
            "artifact_sha256": digest, "github_artifact_digest_matches": True,
            "source_archive_sha256": sha((out / "source.tar.gz").read_bytes()),
            "source_archive_kind": "git archive --format=tar exact-source-commit; deterministic gzip",
            "historical_input_count": 1264, "independent_review_count": 2,
            "all_new_module_summary": coverage["summary"], "project_exact_replays": len(project_counts),
            "project_physical_declarations": sum(project_counts.values()),
            "provider_physical_declarations": sum(provider_counts.values()),
            "provider_exact_replays": len(provider_counts), "official_kernel_exact_module_replays": True,
            "exact_replay_source_sha256": sha(runner_raw),
            "official_checker_source_sha256": OFFICIAL_CHECKER_SOURCE_SHA256,
            "replay_algorithm": "Accepted exact-module runner using LeanChecker.replayFromImports algorithm; CLI prefix selector bypassed",
            "clean_skipped": False, "actual_clean_command": clean[0],
            "checked_raw_log_count": len(commands), "review_binding_keys": keys,
            "checked_source_sha256": checked_sources, "current_source_input_count": len(checked_sources),
            "ci_only_input_count": len(ci_only_inputs),
            "limitations": [
                "CI object/toolchain hashes are recorded, not compared with unrelated local binaries.",
                "Exact-module runner uses the pinned official bundled-kernel algorithm relative to imported environments; historical suppliers and Mathlib are source-bound but not freshly replayed.",
                "Actual universal-cover contractibility and two-sided nerve equivalence are not claimed.",
            ],
        }
        (out / "archive-verification.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    (out / "README.md").write_text(
        "# Full Theorem 1.8: fresh CI and permanent source-bound evidence\n\n"
        f"- Run: <{run['html_url']}>\n- Exact scientific source commit: `{commit}`.\n"
        f"- {len(project_counts)} project and {len(provider_counts)} selected provider modules: fresh exact-module replays with the pinned official kernel algorithm.\n"
        "- Actual complement asphericity, full landmark 5 and Theorem 1.8 checked with two independent source-bound reviews.\n"
        "- 1264 historical inputs, every reviewed binding, command log and artifact digest checked.\n"
        "- Original artifact ZIP, deterministic source archive, full compressed Actions log and metadata retained.\n\n"
        "See archive-verification.json and source-inventory.json for scope, hashes and verification limits.\n")
    (out / "SHA256SUMS").write_text("".join(sha(p.read_bytes()) + "  " + p.name + "\n"
        for p in sorted(out.iterdir()) if p.name != "SHA256SUMS"))
    print(json.dumps({k: v for k, v in report.items() if k != "checked_source_sha256"}, indent=2))


if __name__ == "__main__":
    main()
