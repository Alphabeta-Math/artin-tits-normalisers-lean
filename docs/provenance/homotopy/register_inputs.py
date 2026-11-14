#!/usr/bin/env python3
"""Current homotopy prerequisite and accepted supplier register; no Lean commands."""

from __future__ import annotations
import hashlib
import json
from pathlib import Path

FALSE_FLAGS = [
    "full_landmark_5_proved",
    "full_theorem_1_8_proved",
    "actual_arrangement_asphericity_proved",
    "two_sided_nerve_homotopy_equivalence_proved",
]


def build(root: Path):
    def load(path):
        return json.loads((root / path).read_text())

    def ref(path):
        return {
            "path": path,
            "sha256": hashlib.sha256((root / path).read_bytes()).hexdigest(),
        }

    def check_map(mapping):
        for path, digest in mapping.items():
            assert ref(path)["sha256"] == digest, path

    a_path = "docs/provenance/acceptance-homotopy-colib.json"
    a = load(a_path)
    assert a["accepted"] is True and a["accepted_homotopy_prerequisites"] is False
    assert all(a[k] is False for k in FALSE_FLAGS)
    check_map(a["independent_reviews_sha256"])
    for mapping in a["provider_bindings"].values():
        if isinstance(mapping, dict):
            check_map(mapping)
    d = load("homotopy/vendor/provenance.json")
    assert (
        ref("homotopy/vendor/provenance.json")["sha256"]
        == a["provider_bindings"]["vendor_provenance_sha256"]
    )
    v = load(a["technical_verification_path"])
    assert (
        ref(a["technical_verification_path"])["sha256"]
        == a["technical_verification_sha256"]
        and v["ok"]
    )
    coverage = load("homotopy/evidence/providers/coverage.json")
    assert v["canonical_declarations"] == v["physical_occurrences"] == 338
    files = []
    patches = []
    for f in d["files"]:
        active = "homotopy/vendor/" + f["path"]
        original = "homotopy/vendor/" + f["original_path"]
        patch = "homotopy/vendor/" + f["patch_path"]
        assert (
            ref(active)["sha256"] == f["active_sha256"]
            and ref(original)["sha256"] == f["upstream_sha256"]
            and ref(patch)["sha256"] == f["patch_sha256"]
        )
        files.append(
            {
                "module": f["module"],
                "upstream_module": f["upstream_module"],
                "upstream_path": f["upstream_path"],
                "active_path": active,
                "original_path": original,
                "active_sha256": f["active_sha256"],
                "upstream_sha256": f["upstream_sha256"],
                "actual_active_sha256": ref(active)["sha256"],
                "actual_original_sha256": ref(original)["sha256"],
                "imports": f["imports"],
                "scope": f["selection"],
                "application": f["application"],
            }
        )
        patches.append(
            {
                "module": f["module"],
                "patch": ref(patch),
                "scope": "Entire original module; import-only relocation, no proof/hypothesis port",
            }
        )
    phases = []
    commands = []
    for phase, row in v["records"].items():
        path = "homotopy/" + row["record"]
        assert ref(path)["sha256"] == row["sha256"]
        phases.append({"phase": phase, "record": ref(path)})
        commands.extend(load(path)["commands"])
    supplier = {
        "id": "homotopy-colib-domination-supplier",
        "repository": d["repository"],
        "revision": d["upstream_sha"],
        "module_count": len(files),
        "disposition": "Root-accepted 21-module supplier only after both independent reviews and source-bound technical verification; full M5/asphericity/two-sided nerve equivalence remain unproved",
        "provenance": ref("homotopy/vendor/provenance.json"),
        "source_inventory": ref("homotopy/evidence/providers/coverage.json"),
        "verification": ref(a["technical_verification_path"]),
        "verification_ok": v["ok"],
        "verification_commands": commands,
        "verification_phase_records": phases,
        "license_identifier": d["license"]["identifier"],
        "license_files": [ref("homotopy/vendor/" + d["license"]["path"])],
        "files": files,
        "patches": patches,
        "assembly_script": ref("homotopy/" + d["assembly_script"]),
        "assembly_recipe": ref("homotopy/vendor/" + d["assembly_recipe"]),
        "upstream_metadata": d["upstream_metadata"],
        "internal_source_lineage": d["internal_source_lineage"],
        "exact_project_or_supplier_declaration_inventory": coverage["declarations"],
        "required_declarations": d["required_declarations"],
        "source_inspection": ref("homotopy/evidence/providers/source-inspection.json"),
        "actual_applications": ref("homotopy/evidence/providers/applications.json"),
        "root_acceptance": ref(a_path),
        "independent_reviews_sha256": a["independent_reviews_sha256"],
        "reviewed_authoritative_evidence_count": 42,
        "all_retained_evidence_count": 44,
        "archival_note": "Two extra retained early API-build files are historical, not silently asserted independently reviewed. Initial review B metadata is preserved in reviews/development; normalized final receipt binds both actual application logs.",
        "archive_records": [],
        "accepted_homotopy_prerequisites": False,
        **{k: False for k in FALSE_FLAGS},
    }
    inv_path = "homotopy/source-inventory.json"
    inv = load(inv_path)
    root_path = "docs/theorem18/landmarks/homotopy-prerequisites-root-acceptance.json"
    accepted = load(root_path)
    assert (
        accepted["accepted_homotopy_prerequisites"] is True
        and accepted["mathematical_acceptance"] is True
    )
    assert all(accepted[k] is False and inv[k] is False for k in FALSE_FLAGS)
    assert inv["accepted_homotopy_prerequisites"] is False
    assert accepted["source_inventory_sha256"] == ref(inv_path)["sha256"]
    check_map(accepted["independent_reviews_sha256"])
    for key, value in accepted["source_bindings"].items():
        assert inv[key] == value, key
        if isinstance(value, dict):
            check_map(value)
    technical = load(inv["technical_verification_path"])
    assert (
        ref(inv["technical_verification_path"])["sha256"]
        == inv["technical_verification_sha256"]
    )
    assert (
        technical["ok"]
        and technical["inputs_unchanged"]
        and technical["clean_skipped"] is True
    )
    assert len(technical["commands"]) == 92 and len(technical["exact_replays"]) == 32
    checkpoint = {
        "status": "Root-accepted actual homotopy/ribbon prerequisites; clean final-mode CI pending",
        "accepted_homotopy_prerequisites": True,
        **{k: False for k in FALSE_FLAGS},
        "root_acceptance": ref(root_path),
        "source_inventory": ref(inv_path),
        "technical_verification": ref(inv["technical_verification_path"]),
        "independent_reviews_sha256": accepted["independent_reviews_sha256"],
        "scope": accepted["scope"],
        "remaining_obligation": accepted["remaining_obligation"],
        "physical_summary": inv["physical_summary"],
        "critical_declarations": inv["critical_declarations"],
        "project_source_sha256": inv["project_source_sha256"],
        "old_accepted_context_inputs": 1117,
        "local_clean_skipped": True,
        "local_clean_skip_reason": technical["clean_skip_reason"],
        "local_commands": 92,
        "fresh_exact_module_replays": 32,
        "expected_final_clean_CI_commands": 93,
        "clean_github_ci_status": accepted["clean_github_ci_status"],
        "compiled_dependency_graph": "New versioned complete actual term graph observation authorized; no completed export asserted yet",
    }
    passed = [
        p
        for p in sorted(
            (root / "docs/provenance/homotopy").glob("run-*/execution.json")
        )
        if json.loads(p.read_text()).get("ok")
    ]
    if passed:
        p = passed[-1]
        e = json.loads(p.read_text())
        assert (
            e["baseline_unchanged"]
            and e["inputs_unchanged"]
            and e["old_roots_and_dependency_edges_preserved"]
        )
        checkpoint["compiled_dependency_graph"] = {
            "execution": ref(str(p.relative_to(root))),
            "graph": e["annotated_graph"],
            "raw_graphs": e["raw_graphs"],
            "counts": e["counts"],
            "observed_git_head": e["observed_git_head"],
            "scope": "All earlier project and239newphysical declarations; private/generated/aliases included. Observation confers no full-target proof.",
        }
    publication_path = "docs/provenance/publications/9dacc8befce702eed601430c776da385cab07343/binding.json"
    if (root / publication_path).exists():
        bound = load(publication_path)
        validation_path = str(Path(publication_path).with_name("validation.json"))
        validation = load(validation_path)
        assert (
            bound["ok"]
            and validation["ok"]
            and validation["binding_sha256"] == ref(publication_path)["sha256"]
        )
        assert bound["accepted_homotopy_prerequisites"] is True and all(
            bound[k] is False for k in FALSE_FLAGS
        )
        checkpoint["source_publication"] = {
            "commit": bound["commit"],
            "binding": ref(publication_path),
            "validation": ref(validation_path),
            "exact_Git_blob_bindings": bound["exact_source_binding_count"],
            "historical_metadata_mismatches": list(
                bound["non_scientific_historical_metadata_differences"]
            ),
            "observer_only_metadata_exceptions": list(
                bound["post_publication_observer_metadata"]
            ),
            "CI_status_at_binding_creation": bound["clean_github_ci"],
        }
    closeout_path = (
        root / "docs/theorem18/landmarks/homotopy-prerequisites-closeout.json"
    )
    if closeout_path.exists():
        checkpoint["clean_CI"] = validate_closeout(root, closeout_path)
        checkpoint["clean_github_ci_status"] = "passed"
        checkpoint["status"] = (
            "Root-accepted actual homotopy/ribbon prerequisites; clean final-mode CI passed; all four full-target flags remain false"
        )
        checkpoint["compiled_dependency_graph"]["current_clean_CI_closeout"] = (
            checkpoint["clean_CI"]["closeout"]
        )
        checkpoint["source_publication"]["current_clean_CI_closeout"] = checkpoint[
            "clean_CI"
        ]["closeout"]
    return supplier, checkpoint


def validate_closeout(root: Path, closeout_path: Path):
    """Validate an ACTUAL root archive receipt; never run Lean or rewrite history."""

    def load(path):
        return json.loads((root / path).read_text())

    def ref(path):
        return {
            "path": str(path),
            "sha256": hashlib.sha256((root / path).read_bytes()).hexdigest(),
        }

    false_flags = [
        "two_sided_nerve_homotopy_equivalence_proved",
        "full_landmark_5_proved",
        "actual_arrangement_asphericity_proved",
        "full_theorem_1_8_proved",
    ]
    closed = json.loads(closeout_path.read_text())
    assert (
        closed["clean_ci_passed"] is True
        and closed["accepted_homotopy_prerequisites"] is True
    )
    assert all(closed[k] is False for k in false_flags)
    acceptance_path = (
        "docs/theorem18/landmarks/homotopy-prerequisites-root-acceptance.json"
    )
    inventory_path = "homotopy/source-inventory.json"
    assert (
        closed["local_mathematical_acceptance_sha256"] == ref(acceptance_path)["sha256"]
    )
    assert closed["source_inventory_sha256"] == ref(inventory_path)["sha256"]
    acceptance, inventory = load(acceptance_path), load(inventory_path)
    assert acceptance["accepted_homotopy_prerequisites"] is True
    assert inventory["accepted_homotopy_prerequisites"] is False
    assert all(
        record[k] is False for record in [acceptance, inventory] for k in false_flags
    )
    for key, binding in acceptance["source_bindings"].items():
        assert inventory[key] == binding, key
    for path, digest in acceptance["independent_reviews_sha256"].items():
        assert ref(path)["sha256"] == digest
    directory = Path(closed["ci_archive_directory"])
    assert not directory.is_absolute() and ".." not in directory.parts
    archive_path, final_path = (
        directory / "archive-verification.json",
        directory / "verification.json",
    )
    for path, digest in closed["ci_archive_sha256"].items():
        assert ref(path)["sha256"] == digest, path
    assert (
        str(archive_path) in closed["ci_archive_sha256"]
        and str(final_path) in closed["ci_archive_sha256"]
    )
    archive, final, run = (
        load(archive_path),
        load(final_path),
        load(directory / "run.json"),
    )
    assert archive["ok"] is True and final["ok"] is True
    assert (
        archive["accepted_homotopy_prerequisites"] is True
        and final["accepted_homotopy_prerequisites"] is True
    )
    assert all(record[k] is False for record in [archive, final] for k in false_flags)
    assert final["mode"] == "final" and final["inputs_unchanged"] is True
    assert final["semantic_acceptance_claimed"] is True
    assert (
        closed["source_commit"]
        == archive["source_commit"]
        == final["repository_head"]
        == run["head_sha"]
        == "9dacc8befce702eed601430c776da385cab07343"
    )
    assert run["conclusion"] == "success" and run["status"] == "completed"
    assert closed["github_run_id"] == archive["run_id"] == run["id"] == 43590812660
    assert closed["github_run_url"] == archive["run_url"] == run["html_url"]
    assert (
        archive["github_artifact_digest_matches"] is True
        and closed["artifact_digest_matches_github"] is True
    )
    archives = [path for path in closed["ci_archive_sha256"] if path.endswith(".zip")]
    assert (
        len(archives) == 1 and ref(archives[0])["sha256"] == archive["artifact_sha256"]
    )
    assert (
        len(archive["checked_source_sha256"])
        == archive["current_source_input_count"]
        == closed["archive_checked_current_input_count"]
    )
    for path, digest in archive["checked_source_sha256"].items():
        assert ref(path)["sha256"] == digest, path
    assert (
        archive["checked_source_sha256"][inventory_path]
        == closed["source_inventory_sha256"]
    )
    historical = load(
        "docs/theorem18/landmarks/github-evidence/run-43579352641/archive-verification.json"
    )["checked_source_sha256"]
    assert final["accepted_context_input_sha256"] == historical
    assert len(historical) == archive["historical_input_count"] == 1117
    for path, digest in historical.items():
        assert archive["checked_source_sha256"][path] == digest
    for key, binding in final["source_bindings"].items():
        assert inventory[key] == binding, key
    for key in archive["review_binding_keys"]:
        assert acceptance["source_bindings"][key] == inventory[key]
        binding = inventory[key]
        if isinstance(binding, dict):
            for path, digest in binding.items():
                assert archive["checked_source_sha256"][path] == digest, (key, path)
    assert (
        archive["independent_review_count"]
        == closed["independent_statement_reviews_accepted"]
        == 2
    )
    assert (
        final["project_statement_reviews_sha256"]
        == acceptance["independent_reviews_sha256"]
    )
    assert archive["project_summary"] == inventory["physical_summary"]
    assert (
        archive["project_summary"]["canonical_project_declarations"]
        == archive["project_summary"]["physical_occurrences"]
        == 239
    )
    provider = load("homotopy/evidence/providers/coverage.json")
    assert final["provider_physical_summary"] == provider["summary"]
    assert (
        provider["summary"]["canonical_declarations"]
        == provider["summary"]["physical_occurrences"]
        == archive["provider_declarations"]
        == 338
    )
    counts = {
        module: len(names)
        for module, names in inventory[
            "compiled_declaration_occurrences_by_module"
        ].items()
    }
    assert (
        len(counts)
        == closed["project_exact_replays"]
        == archive["project_exact_replays"]
        == 11
    )
    counts.update(
        {row["module"]: row["declarations"] for row in provider["physical_modules"]}
    )
    assert closed["provider_exact_replays"] == archive["provider_exact_replays"] == 21
    assert len(final["exact_replays"]) == len(counts) == 32
    assert {row["module"] for row in final["exact_replays"]} == set(counts)
    for row in final["exact_replays"]:
        result = row["result"]
        assert (
            row["physical_declarations_expected"]
            == result["declarations"]
            == counts[row["module"]]
        )
        assert (
            result["module"] == row["module"]
            and result["exact"] is True
            and result["kernel_replay_passed"] is True
        )
    assert (
        len(final["commands"])
        == archive["checked_raw_log_count"]
        == closed["archive_checked_raw_log_count"]
        == 93
    )
    assert all(row["exit_code"] == 0 for row in final["commands"])
    assert (
        final["clean_skipped"] is False and closed["clean_skipped_in_final_ci"] is False
    )
    clean = [row for row in final["commands"] if row["label"] == "clean-new-package"]
    assert len(clean) == 1 and clean[0]["argv"] == ["lake", "clean", "artin-homotopy"]
    assert clean[0] == archive["actual_clean_command"] == closed["actual_clean_command"]

    return {
        "status": "passed",
        "closeout": ref(str(closeout_path.relative_to(root))),
        "archive_verification": ref(archive_path),
        "final_verification": ref(final_path),
        "source_commit": closed["source_commit"],
        "run_url": closed["github_run_url"],
        "artifact_sha256": archive["artifact_sha256"],
        "checked_current_inputs": archive["current_source_input_count"],
        "unchanged_historical_inputs": 1117,
        "checked_raw_logs": 93,
        "project_exact_replays": 11,
        "provider_exact_replays": 21,
        "project_declarations": 239,
        "provider_declarations": 338,
        "accepted_homotopy_prerequisites": True,
        **{key: False for key in false_flags},
        "clean_skipped": False,
        "actual_clean_command": clean[0],
        "limits": "Actual final-mode prerequisite CI only; old suppliers/Mathlib were not freshly replayed, and actual arrangement asphericity/full M5/Theorem 1.8 remain unproved.",
    }
