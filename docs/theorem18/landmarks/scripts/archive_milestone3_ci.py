#!/usr/bin/env python3
"""Preserve and validate an actual successful landmark-3 Actions artifact."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile

BASE = Path(__file__).resolve().parents[4]
REPO = "lazyinspirit/artin-tits-normalisers-lean"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def gh(*args):
    return subprocess.check_output(["gh", *args], cwd=BASE)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run_id", type=int)
    args = parser.parse_args()
    out = BASE / "docs/theorem18/landmarks/github-evidence" / f"run-{args.run_id}"
    out.mkdir(parents=True, exist_ok=False)

    def metadata(name, endpoint):
        raw = gh("api", endpoint)
        (out / name).write_bytes(raw)
        return json.loads(raw)

    run = metadata("run.json", f"/repos/{REPO}/actions/runs/{args.run_id}")
    require(run["status"] == "completed" and run["conclusion"] == "success", "Run not successful")
    require(run["path"] == ".github/workflows/chambers.yml", "Wrong workflow")
    jobs = metadata("jobs.json", f"/repos/{REPO}/actions/runs/{args.run_id}/jobs")
    require(jobs["total_count"] == 1 and all(j["conclusion"] == "success" for j in jobs["jobs"]), "Wrong jobs")
    arts = metadata("artifacts.json", f"/repos/{REPO}/actions/runs/{args.run_id}/artifacts")
    selected = [a for a in arts["artifacts"] if a["name"] == "lean-landmark3-verification"]
    require(len(selected) == 1 and not selected[0]["expired"], "Artifact missing/ambiguous/expired")
    artifact = selected[0]
    archive_path = out / "landmark3-verification.zip"
    with archive_path.open("wb") as stream:
        subprocess.run(["gh", "api", f'/repos/{REPO}/actions/artifacts/{artifact["id"]}/zip'],
                       cwd=BASE, stdout=stream, check=True)
    digest = sha(archive_path.read_bytes())
    require(artifact["digest"] == "sha256:" + digest, "GitHub artifact digest differs")
    with gzip.GzipFile(filename=str(out / "actions.log.gz"), mode="wb", mtime=0) as stream:
        stream.write(gh("run", "view", str(args.run_id), "--log"))
    checked_sources = {}
    with zipfile.ZipFile(archive_path) as archive:
        def raw(path):
            return archive.read(path)

        def read(path):
            return json.loads(raw(path))

        result = read("verification.json")
        require(result["ok"] is True and result["inputs_unchanged"] is True
                and result["mode"] == "final" and result["full_landmark_3_proved"] is True
                and result["semantic_acceptance_claimed"] is True
                and result["full_theorem_1_8_proved"] is False, "Wrong scope/result")
        require(result["repository_head"] == run["head_sha"], "Wrong source commit")
        commands = result["commands"]
        require(commands and all(c["exit_code"] == 0 for c in commands), "Failed command")
        for command in commands:
            require(sha(raw(command["log"])) == command["log_sha256"], "Changed command log")
        require(sha(raw("inputs.json")) == result["inputs_sha256"], "Input manifest changed")
        require(sha(raw("project-coverage.json")) == result["project_coverage_sha256"], "Coverage changed")
        inputs = read("inputs.json")
        coverage = read("project-coverage.json")
        inv = json.loads((BASE / "chambers/source-inventory.json").read_text())
        for key in ["audited_declarations_by_module", "compiled_declaration_occurrences_by_module",
                    "compiled_duplicate_equivalences"]:
            require(coverage[key] == inv[key], "Frozen inventory coverage differs")
        bindings = result["source_bindings"]
        for key in ["project_source_sha256", "configuration_sha256", "provider_active_source_sha256",
                    "provider_original_source_sha256", "provider_import_patch_sha256"]:
            require(bindings[key] == inv[key], "Frozen source inventory differs: " + key)
        require(bindings["vendor_provenance_sha256"] == inv["vendor_provenance_sha256"], "Provider inventory changed")
        require(len(result["accepted_context_input_sha256"]) == 855, "Wrong historical context")
        # Source paths in the command/input record are runner-absolute. Remap
        # only within this run's actual checkout; compiled binaries are retained
        # as CI hashes, never compared to unrelated local build output.
        runner_base = Path(commands[0]["cwd"]).parent
        runner_output = runner_base / "chambers/evidence/landmark3-ci"
        for absolute, expected in inputs["source_and_records_sha256"].items():
            path = Path(absolute)
            if path.is_relative_to(runner_output):
                require(sha(raw(str(path.relative_to(runner_output)))) == expected, "Changed embedded replay source")
            elif path.is_relative_to(runner_base):
                relative = path.relative_to(runner_base)
                if ".lake" in relative.parts:
                    continue
                require(sha((BASE / relative).read_bytes()) == expected, "Current source changed: " + str(relative))
                checked_sources[str(relative)] = expected
        for key in ["accepted_context_input_sha256", "historical_reviews_sha256",
                    "provider_statement_reviews_sha256", "project_statement_reviews_sha256"]:
            for path, expected in result[key].items():
                require(checked_sources.get(path) == expected, "Unbound source/review: " + path)
        require(checked_sources.get("chambers/source-inventory.json") == sha((BASE / "chambers/source-inventory.json").read_bytes()),
                "Final inventory not bound")
        providers = json.loads((BASE / "chambers/vendor/provenance.json").read_text())
        counts = {m: len(names) for m, names in inv["compiled_declaration_occurrences_by_module"].items()}
        provider_counts = {r["module"]: r["declarations"] for r in
                           json.loads((BASE / "chambers/evidence/providers/coverage.json").read_text())["physical_modules"]}
        counts.update(provider_counts)
        replays = result["exact_replays"]
        require(len(replays) == len(counts) and {r["module"] for r in replays} == set(counts), "Replay coverage differs")
        for row in replays:
            r = row["result"]
            require(r["module"] == row["module"] and r["exact"] is True and r["kernel_replay_passed"] is True
                    and r["declarations"] == row["physical_declarations_expected"] == counts[row["module"]],
                    "Replay result/count differs")
        require(len(provider_counts) == providers["module_count"] == 9
                and sum(provider_counts.values()) == 232, "Provider coverage differs")
        for label in ["a", "b"]:
            review = json.loads((BASE / f"chambers/reviews/landmark3-{label}.json").read_text())
            require(review["verdict"] == "accept-landmark3" and review["model"] == "gpt-6.1-sol"
                    and review["reasoning_effort"] == "high" and review["full_landmark_3_proved"] is True
                    and review["full_theorem_1_8_proved"] is False
                    and review["source_inventory_sha256"] == checked_sources["chambers/source-inventory.json"],
                    "Wrong independent review")
        (out / "verification.json").write_bytes(raw("verification.json"))
        report = {"ok": True, "run_id": args.run_id, "run_url": run["html_url"],
                  "source_commit": run["head_sha"], "full_landmark_3_proved": True,
                  "full_theorem_1_8_proved": False, "artifact_sha256": digest,
                  "github_artifact_digest_matches": True, "current_source_input_count": len(checked_sources),
                  "historical_input_count": 855, "independent_review_count": 2,
                  "project_summary": coverage["summary"], "project_exact_replays": len(counts) - 9,
                  "provider_exact_replays": 9, "provider_declarations": 232,
                  "checked_raw_log_count": len(commands), "checked_source_sha256": checked_sources,
                  "limitations": ["CI compiled hashes recorded, not compared to unrelated local compiled binaries.",
                      "Bundled kernel relative to imported environments; old accepted suppliers and Mathlib not freshly replayed."]}
        (out / "archive-verification.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    (out / "README.md").write_text(
        "# Landmark 3: fresh CI and permanent proof records\n\n"
        "Actual equivariant interval/ribbon/orbit groupoid comparison and strictly commuting covering square. "
        "The literal adjacent-gallery dictionary, landmarks 4/5 and full Theorem 1.8 remain unclaimed.\n\n"
        f'- Run: <{run["html_url"]}>\n- Source commit: `{run["head_sha"]}`.\n'
        f'- {len(counts) - 9} project and 9 new supplier exact-module replays passed.\n'
        "- Both independent source-bound reviews, all current scientific inputs and 855 unchanged historical inputs checked.\n"
        "- The original artifact ZIP, complete compressed Actions log and run/job/artifact metadata are retained.\n\n"
        "See archive-verification.json for exact declaration counts, source/log hashes and verification limits.\n")
    (out / "SHA256SUMS").write_text("".join(sha(p.read_bytes()) + "  " + p.name + "\n"
        for p in sorted(out.iterdir()) if p.name != "SHA256SUMS"))
    print(json.dumps({k: v for k, v in report.items() if k != "checked_source_sha256"}, indent=2))


if __name__ == "__main__":
    main()
