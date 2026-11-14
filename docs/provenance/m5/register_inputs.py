#!/usr/bin/env python3
"""Read-only M5 source/search index. Search inspection never grants acceptance."""

from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path


def build(root: Path):
    def ref(path):
        return {
            "path": path,
            "sha256": hashlib.sha256((root / path).read_bytes()).hexdigest(),
        }

    records = []
    repositories = {}

    def add(
        repository,
        revision=None,
        role="M5 search encounter only; exact inspection/use limits in inventory",
    ):
        if not isinstance(repository, str):
            return
        name = (
            repository.removeprefix("https://github.com/")
            .removesuffix(".git")
            .rstrip("/")
        )
        if not re.fullmatch(r"[\w.-]+/[\w.-]+", name) or name.endswith(
            (".lean", ".md", ".json", ".toml", ".py")
        ):
            return
        item = repositories.setdefault(
            "https://github.com/" + name, {"roles": set(), "exact_revisions": set()}
        )
        item["roles"].add(role)
        if isinstance(revision, str) and re.fullmatch(r"[0-9a-f]{40}", revision):
            item["exact_revisions"].add(revision)

    for path in sorted((root / "docs/provenance/searches").glob("m5*-inventory.json")):
        data = json.loads(path.read_text())
        records.append({"inventory": ref(str(path.relative_to(root))), "records": data})
        repos = data.get("repositories", data.get("repositories_inspected", []))
        if isinstance(repos, dict):
            for name, item in repos.items():
                for revision in item.get("revisions", {}):
                    add(item.get("repository", name), revision)
                if not item.get("revisions"):
                    add(item.get("repository", name))
        else:
            for item in repos:
                add(item["repository"], item.get("pin", item.get("commit")))
        # These are exact repository-valued fields, not arbitrary source paths.
        for item in data.get("pinned_metadata", []):
            add(
                item.get("repo"),
                item.get("sha"),
                "M5 inspected candidate metadata; not a used dependency",
            )
            for package in item.get("packages", []):
                add(
                    package.get("url"),
                    package.get("rev"),
                    "M5 candidate transitive pin only; not a project dependency",
                )
    for item in repositories.values():
        item["roles"] = sorted(item["roles"])
        item["exact_revisions"] = sorted(item["exact_revisions"])
    checkpoint = {
        "status": "Prerequisite source development/static infrastructure; main source acceptance and CI not yet claimed",
        "accepted_asphericity_prerequisites": False,
        "full_landmark_5_proved": False,
        "full_theorem_1_8_proved": False,
        "actual_arrangement_asphericity_proved": False,
        "plan": ref("docs/theorem18/landmarks/milestone5-PLAN.md"),
        "unproved_core": "Actual higher-homotopy vanishing or contraction of ComplementUniversalCover M J; the Deligne lifted nerve/combinatorial comparison remains unformalized.",
        "new_compiled_dependency_graph": "Not exported yet; immutable through-M2/M3/M4 graphs do not include these new sources.",
    }
    provenance = root / "asphericity/vendor/provenance.json"
    if provenance.exists():
        checkpoint["supplier_provenance"] = ref(str(provenance.relative_to(root)))
        checkpoint["supplier_status"] = (
            "Technically verified and independently supplier-reviewed; root supplier acceptance separate"
        )
        checkpoint["supplier_complete_file_patch_license_endpoint_inventory"] = (
            json.loads(provenance.read_text())
        )
        checkpoint["supplier_technical_verification"] = ref(
            "asphericity/evidence/providers/verification.json"
        )
        checkpoint["supplier_reviews"] = [
            ref(f"asphericity/reviews/providers-{a}.{ext}")
            for a in ["a", "b"]
            for ext in ["json", "md"]
            if (root / f"asphericity/reviews/providers-{a}.{ext}").exists()
        ]
    inventory_path = root / "asphericity/source-inventory.json"
    if inventory_path.exists():
        inventory = json.loads(inventory_path.read_text())
        assert all(
            inventory[k] is False
            for k in [
                "accepted_asphericity_prerequisites",
                "full_landmark_5_proved",
                "full_theorem_1_8_proved",
                "actual_arrangement_asphericity_proved",
            ]
        )
        technical_path = inventory["technical_verification_path"]
        technical = json.loads((root / technical_path).read_text())
        assert (
            technical["ok"]
            and technical["inputs_unchanged"]
            and technical["mode"] == "technical"
        )
        assert (
            hashlib.sha256((root / technical_path).read_bytes()).hexdigest()
            == inventory["technical_verification_sha256"]
        )
        for path, digest in inventory["project_source_sha256"].items():
            assert hashlib.sha256((root / path).read_bytes()).hexdigest() == digest
        checkpoint.update(
            status="Frozen technically verified prerequisite candidate; final project acceptance and clean CI separate",
            source_inventory=ref(str(inventory_path.relative_to(root))),
            technical_verification=ref(technical_path),
            physical_summary=inventory["physical_summary"],
            critical_declarations=inventory["critical_declarations"],
            project_source_sha256=inventory["project_source_sha256"],
            scope=inventory["scope"],
            unproved_core=inventory["unproved_core"],
            old_accepted_context_inputs=996,
            exact_new_module_replays=len(technical["exact_replays"]),
        )
    acceptance_path = (
        root / "docs/theorem18/landmarks/milestone5-prerequisites-root-acceptance.json"
    )
    if acceptance_path.exists():
        acceptance = json.loads(acceptance_path.read_text())
        assert acceptance["accepted_asphericity_prerequisites"] is True
        assert all(
            acceptance[k] is False
            for k in [
                "full_landmark_5_proved",
                "full_theorem_1_8_proved",
                "actual_arrangement_asphericity_proved",
            ]
        )
        assert (
            acceptance["source_inventory_sha256"]
            == ref("asphericity/source-inventory.json")["sha256"]
        )
        for path, digest in acceptance["independent_reviews_sha256"].items():
            assert ref(path)["sha256"] == digest
        checkpoint.update(
            status="Root-accepted asphericity prerequisites only; clean CI separate and full actual-space target remains unproved",
            accepted_asphericity_prerequisites=True,
            root_acceptance=ref(str(acceptance_path.relative_to(root))),
            independent_reviews_sha256=acceptance["independent_reviews_sha256"],
            clean_github_ci_status=acceptance["clean_github_ci_status"],
        )
    exports = sorted((root / "docs/provenance/m5").glob("run-*/execution.json"))
    passed = [p for p in exports if json.loads(p.read_text()).get("ok")]
    if passed:
        path = passed[-1]
        execution = json.loads(path.read_text())
        assert (
            execution["inputs_unchanged"]
            and execution["baseline_unchanged"]
            and execution["old_roots_and_dependency_edges_preserved"]
        )
        checkpoint["new_compiled_dependency_graph"] = {
            "execution": ref(str(path.relative_to(root))),
            "graph": execution["annotated_graph"],
            "raw_graphs": execution["raw_graphs"],
            "counts": execution["counts"],
            "observed_git_head": execution["observed_git_head"],
            "scope": "Complete actual project constants through the implemented prerequisite checkpoint; full M5 and actual arrangement asphericity remain unproved",
            "old_graphs_unchanged": True,
        }
    publication = (
        root
        / "docs/provenance/publications/3165671b648d24521a78d71aac47bd61d0500251/binding.json"
    )
    if publication.exists():
        bound = json.loads(publication.read_text())
        validation_path = publication.with_name("validation.json")
        validation = json.loads(validation_path.read_text())
        assert (
            bound["ok"]
            and validation["ok"]
            and validation["binding_sha256"]
            == ref(str(publication.relative_to(root)))["sha256"]
        )
        assert bound["accepted_asphericity_prerequisites"] is True and all(
            bound[k] is False
            for k in [
                "full_landmark_5_proved",
                "full_theorem_1_8_proved",
                "actual_arrangement_asphericity_proved",
            ]
        )
        checkpoint["source_publication"] = {
            "commit": bound["commit"],
            "binding": ref(str(publication.relative_to(root))),
            "validation": ref(str(validation_path.relative_to(root))),
            "exact_git_blob_bindings": bound["exact_source_binding_count"],
            "historical_metadata_exceptions": list(
                bound["non_scientific_historical_metadata_differences"]
            ),
            "clean_CI_at_binding_creation": bound["clean_github_ci"],
            "precommit_observation_unchanged": True,
        }
    closeout_path = (
        root / "docs/theorem18/landmarks/milestone5-prerequisites-closeout.json"
    )
    if closeout_path.exists():
        checkpoint["clean_CI"] = validate_closeout(root, closeout_path)
        checkpoint.update(
            status="Root-accepted asphericity prerequisites; clean final-mode CI passed; actual arrangement asphericity/full M5/Theorem 1.8 remain unproved",
            clean_github_ci_status="passed",
        )
        checkpoint["new_compiled_dependency_graph"]["current_clean_CI_closeout"] = (
            checkpoint["clean_CI"]["closeout"]
        )
        checkpoint["source_publication"]["current_clean_CI_closeout"] = checkpoint[
            "clean_CI"
        ]["closeout"]
    return records, repositories, checkpoint


def accepted_supplier(root: Path):
    """Promote only the root-accepted eleven-module supplier, never the full target."""
    receipt_path = root / "docs/provenance/acceptance-landmark5-topology.json"
    if not receipt_path.exists():
        return None

    def load(path):
        return json.loads((root / path).read_text())

    def sha(path):
        return hashlib.sha256((root / path).read_bytes()).hexdigest()

    def ref(path):
        return {"path": path, "sha256": sha(path)}

    receipt = load(str(receipt_path.relative_to(root)))
    assert receipt["accepted"] is True
    for key in [
        "accepted_asphericity_prerequisites",
        "full_landmark_5_proved",
        "full_theorem_1_8_proved",
        "actual_arrangement_asphericity_proved",
    ]:
        assert receipt[key] is False
    for path, digest in receipt["independent_reviews_sha256"].items():
        assert sha(path) == digest
    for key, mapping in receipt["provider_bindings"].items():
        if isinstance(mapping, dict):
            for path, digest in mapping.items():
                assert sha(path) == digest, (key, path)
    bindings = receipt["provider_bindings"]
    assert sha("asphericity/ProviderAudit.lean") == bindings["provider_audit_sha256"]
    assert (
        sha(receipt["technical_verification_path"])
        == receipt["technical_verification_sha256"]
    )
    d = load("asphericity/vendor/provenance.json")
    assert (
        sha("asphericity/vendor/provenance.json") == receipt["vendor_provenance_sha256"]
    )
    assert (
        sha("asphericity/vendor/" + d["license"]["path"])
        == d["license"]["sha256"]
        == bindings["provider_license_sha256"]
    )
    v = load("asphericity/evidence/providers/verification.json")
    coverage = load("asphericity/evidence/providers/coverage.json")
    assert v["ok"] and v["canonical_declarations"] == v["physical_occurrences"] == 310
    files, patches = [], []
    for f in d["files"]:
        active = "asphericity/vendor/" + f["path"]
        original = "asphericity/vendor/" + f["original_path"]
        patch = "asphericity/vendor/" + f["patch_path"]
        assert (
            sha(active) == f["active_sha256"]
            and sha(original) == f["upstream_sha256"]
            and sha(patch) == f["patch_sha256"]
        )
        files.append(
            {
                "module": f["module"],
                "upstream_module": f["upstream_module"],
                "upstream_path": f["upstream_path"],
                "active_path": active,
                "original_path": original,
                "active_sha256": sha(active),
                "upstream_sha256": sha(original),
                "actual_active_sha256": sha(active),
                "actual_original_sha256": sha(original),
                "imports": f["imports"],
                "scope": f["selection"],
            }
        )
        patches.append(
            {
                "module": f["module"],
                "patch": ref(patch),
                "scope": "Entire original module, import-path relocation only",
            }
        )
    phases, commands = [], []
    for phase, record in v["records"].items():
        path = "asphericity/" + record["record"]
        assert sha(path) == record["sha256"]
        data = load(path)
        phases.append({"phase": phase, "record": ref(path)})
        commands.extend(data["commands"])
    return {
        "id": "landmark5-topology-prerequisite-supplier",
        "repository": d["repository"],
        "revision": d["upstream_sha"],
        "module_count": len(files),
        "disposition": "Root-accepted unchanged topology suppliers after both independent reviews; no actual arrangement asphericity, full M5 or Theorem 1.8 acceptance",
        "provenance": ref("asphericity/vendor/provenance.json"),
        "source_inventory": ref("asphericity/evidence/providers/coverage.json"),
        "verification": ref("asphericity/evidence/providers/verification.json"),
        "verification_ok": v["ok"],
        "verification_commands": commands,
        "verification_phase_records": phases,
        "license_identifier": d["license"]["identifier"],
        "license_files": [ref("asphericity/vendor/" + d["license"]["path"])],
        "files": files,
        "patches": patches,
        "assembly_script": ref("asphericity/" + d["assembly_script"]),
        "assembly_recipe": ref("asphericity/vendor/" + d["assembly_recipe"]),
        "reused_accepted_sources": d["reused_pinned_dependencies"],
        "exact_project_or_supplier_declaration_inventory": coverage["declarations"],
        "required_declarations": d["required_declarations"],
        "source_inspection": ref(
            "asphericity/evidence/providers/source-inspection.json"
        ),
        "actual_applications": ref("asphericity/evidence/providers/applications.json"),
        "root_acceptance": ref(str(receipt_path.relative_to(root))),
        "independent_reviews_sha256": receipt["independent_reviews_sha256"],
        "archive_records": [],
        "accepted_asphericity_prerequisites": False,
        "full_landmark_5_proved": False,
        "full_theorem_1_8_proved": False,
        "actual_arrangement_asphericity_proved": False,
    }


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
        "full_landmark_5_proved",
        "actual_arrangement_asphericity_proved",
        "full_theorem_1_8_proved",
    ]
    closed = json.loads(closeout_path.read_text())
    assert (
        closed["clean_ci_passed"] is True
        and closed["accepted_asphericity_prerequisites"] is True
    )
    assert all(closed[k] is False for k in false_flags)
    acceptance_path = (
        "docs/theorem18/landmarks/milestone5-prerequisites-root-acceptance.json"
    )
    inventory_path = "asphericity/source-inventory.json"
    assert (
        closed["local_mathematical_acceptance_sha256"] == ref(acceptance_path)["sha256"]
    )
    assert closed["source_inventory_sha256"] == ref(inventory_path)["sha256"]
    acceptance, inventory = load(acceptance_path), load(inventory_path)
    assert acceptance["accepted_asphericity_prerequisites"] is True
    assert inventory["accepted_asphericity_prerequisites"] is False
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
        archive["accepted_asphericity_prerequisites"] is True
        and final["accepted_asphericity_prerequisites"] is True
    )
    assert all(record[k] is False for record in [archive, final] for k in false_flags)
    assert final["mode"] == "final" and final["inputs_unchanged"] is True
    assert final["semantic_acceptance_claimed"] is True
    assert (
        closed["source_commit"]
        == archive["source_commit"]
        == final["repository_head"]
        == run["head_sha"]
        == "3165671b648d24521a78d71aac47bd61d0500251"
    )
    assert run["conclusion"] == "success" and run["status"] == "completed"
    assert closed["github_run_id"] == archive["run_id"] == run["id"] == 43579352641
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
        "docs/theorem18/landmarks/github-evidence/run-43573814974/archive-verification.json"
    )["checked_source_sha256"]
    assert final["accepted_context_input_sha256"] == historical
    assert len(historical) == archive["historical_input_count"] == 996
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
        == 138
    )
    provider = load("asphericity/evidence/providers/coverage.json")
    assert final["provider_physical_summary"] == provider["summary"]
    assert (
        provider["summary"]["canonical_declarations"]
        == provider["summary"]["physical_occurrences"]
        == archive["provider_declarations"]
        == 310
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
        == 8
    )
    counts.update(
        {row["module"]: row["declarations"] for row in provider["physical_modules"]}
    )
    assert closed["provider_exact_replays"] == archive["provider_exact_replays"] == 11
    assert len(final["exact_replays"]) == len(counts) == 19
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
        == 67
    )
    assert all(row["exit_code"] == 0 for row in final["commands"])
    return {
        "status": "passed",
        "closeout": ref(str(closeout_path.relative_to(root))),
        "archive_verification": ref(archive_path),
        "final_verification": ref(final_path),
        "source_commit": closed["source_commit"],
        "run_url": closed["github_run_url"],
        "artifact_sha256": archive["artifact_sha256"],
        "checked_current_inputs": archive["current_source_input_count"],
        "unchanged_historical_inputs": 996,
        "checked_raw_logs": 67,
        "project_exact_replays": 8,
        "provider_exact_replays": 11,
        "project_declarations": 138,
        "provider_declarations": 310,
        "accepted_asphericity_prerequisites": True,
        **{key: False for key in false_flags},
        "limits": "Actual final-mode prerequisite CI only; old suppliers/Mathlib were not freshly replayed, and actual arrangement asphericity/full M5/Theorem 1.8 remain unproved.",
    }
