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
    return supplier, checkpoint
