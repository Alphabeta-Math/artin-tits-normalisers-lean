#!/usr/bin/env python3
"""Validate source bindings and raw provider build/audit/replay evidence."""

import datetime
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
EVIDENCE = ROOT / "evidence/providers/weights"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    provenance = json.loads((ROOT / "vendor/provenance-weights.json").read_text())
    modules = provenance["topological_order"]
    records = {}
    for phase in ["build", "audit", "replay"]:
        path = sorted(EVIDENCE.glob(phase + "-*/verification.json"))[-1]
        record = json.loads(path.read_text())
        assert record["ok"] and record["inputs_unchanged"]
        assert record["modules"] == modules
        assert record["commands"][0]["command"] == ["python3", "scripts/providers/weights/assemble.py", "--check"]
        for command in record["commands"]:
            assert command["exit_code"] == 0
            assert digest(path.parent / command["log"]) == command["log_sha256"]
        records[phase] = {"record": str(path.relative_to(ROOT)), "sha256": digest(path), "data": record}
    assert records["build"]["data"]["commands"][1]["command"] == ["lake", "build", *modules]
    assert records["audit"]["data"]["commands"][1]["command"] == ["lake", "env", "lean", "WeightsProviderAudit.lean"]
    replay = records["replay"]
    assert len(replay["data"]["commands"]) == len(modules) + 1
    for module, command in zip(modules, replay["data"]["commands"][1:]):
        assert command["command"] == ["lake", "env", "leanchecker", "--verbose", module]
        log = (ROOT / replay["record"]).parent / command["log"]
        assert log.read_text().splitlines()[0] == "replaying " + module
    audit = records["audit"]
    audit_log = (ROOT / audit["record"]).parent / audit["data"]["commands"][1]["log"]
    text = audit_log.read_text()
    def parse(prefix):
        return [json.loads(line.split(prefix, 1)[1]) for line in text.splitlines() if prefix in line]
    declarations = parse("WEIGHTS_PROVIDER_DECL_JSON ")
    physical = parse("WEIGHTS_PROVIDER_PHYSICAL_MODULE_JSON ")
    summaries = parse("WEIGHTS_PROVIDER_PHYSICAL_SUMMARY_JSON ")
    duplicates = parse("WEIGHTS_PROVIDER_PHYSICAL_DUPLICATE_JSON ")
    names = {row["name"] for row in declarations}
    physical_names = {name for row in physical for name in row["names"]}
    assert names and len(names) == len(declarations)
    assert {row["module"] for row in physical} == set(modules)
    assert names == physical_names
    required = set(provenance["required_declarations"])
    assert required <= names
    assert len(summaries) == 1
    summary = summaries[0]
    assert summary["canonical_declarations"] == len(declarations)
    assert summary["physical_occurrences"] == sum(row["declarations"] for row in physical)
    assert summary["distinct_physical_names"] == len(names)
    assert summary["identical_theorem_duplicates"] == len(duplicates)
    assert summary["canonical_axioms_checked"]
    assert summary["all_physical_type_value_universe_parameters_identical"]
    for row in declarations:
        assert set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
    for file in provenance["files"]:
        assert digest(ROOT / "vendor" / file["path"]) == file["active_sha256"]
        assert digest(ROOT / "vendor" / file["original_path"]) == file["upstream_sha256"]
        assert digest(ROOT / "vendor" / file["patch_path"]) == file["patch_sha256"]
    assert digest(ROOT / "vendor" / provenance["license"]["path"]) == provenance["license"]["sha256"]
    assert digest(ROOT / provenance["assembly_script"]) == provenance["assembly_script_sha256"]
    assert digest(ROOT / "vendor" / provenance["assembly_recipe"]) == provenance["assembly_recipe_sha256"]
    before = json.loads(((ROOT / audit["record"]).parent / "inputs-before.json").read_text())
    after = json.loads(((ROOT / replay["record"]).parent / "inputs-after.json").read_text())
    assert before == after
    coverage = {"declarations": declarations, "physical_modules": physical,
                "duplicates": duplicates, "summary": summary}
    (EVIDENCE / "coverage.json").write_text(json.dumps(coverage, indent=2) + "\n")
    result = {
        "ok": True, "created_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "repository": provenance["repository"], "upstream_sha": provenance["upstream_sha"],
        "provenance": "vendor/provenance-weights.json", "provenance_sha256": digest(ROOT / "vendor/provenance-weights.json"),
        "harness": "WeightsProviderAudit.lean", "harness_sha256": digest(ROOT / "WeightsProviderAudit.lean"),
        "module_count": len(modules), "canonical_declarations": len(declarations),
        "physical_occurrences": summary["physical_occurrences"],
        "identical_duplicates": len(duplicates),
        "axioms_allowed": ["propext", "Classical.choice", "Quot.sound"],
        "audit_through_replay_inputs_identical": True,
        "coverage_file": "evidence/providers/weights/coverage.json", "coverage_sha256": digest(EVIDENCE / "coverage.json"),
        "environment_file": "evidence/providers/weights/environment.json", "environment_sha256": digest(EVIDENCE / "environment.json"),
        "kernel_replay_workers": 1,
        "replay_mode": "one exact module per fresh official leanchecker process",
        "kernel_replay_relative_to_imports": True, "independent_kernel_implementation": False,
        "independent_statement_reviews_pending": True, "root_mathematical_acceptance_pending": True,
        "full_landmark_5_proved": False, "full_theorem_1_8_proved": False,
        "source_ports": "Entire upstream source modules; selected import relocation and one recorded Lean-version tactic compatibility block",
        "source_inspection_file": "evidence/providers/weights/source-inspection.json",
        "source_inspection_sha256": digest(EVIDENCE / "source-inspection.json"),
        "records": {phase: {key: value for key, value in record.items() if key != "data"}
                    for phase, record in records.items()},
    }
    (EVIDENCE / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
