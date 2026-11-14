#!/usr/bin/env python3
"""Freeze observed technical coverage for prerequisite review; never full M5 acceptance."""

from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[3]
ROOT = BASE / "homotopy"
PREFIX = "ArtinNormalisers.Homotopy5."
CRITICAL = [
    PREFIX + name
    for name in [
        "actualLocalEquiconnection",
        "actualNerveCover_pointStarRefines",
        "actualMetricNerve",
        "actualNerveForward",
        "actualNerveReturn",
        "actualNerveDominationHomotopy",
        "actualNerveForward_homotopyGroupMap_injective",
        "complement_isAspherical_of_actualNerve_higher_vanishing",
        "homotopyGroupMap_injective_of_domination",
        "isAspherical_of_dominated_by_aspherical",
        "mem_tubeSet_iff_chamberBetween",
        "positive_reduced_ribbon_lcm_left_with_tails",
        "positive_reduced_ribbon_gcd_left_with_tails",
        "greatest_simple_ribbon_prefix_with_tail",
        "maximalFacePrefix_greatest",
        "maximalFacePrefix_tail_degree_lt",
        "geometricRepresentation_apply_outside_parabolic",
        "parabolicLongest_positive_supported_negative",
        "canonicalDominant_root_zero_iff_support",
        "fiberTarget_facePrefix_oppositeAtFace",
        "rawFacePoint_incident_iff_ribbonPrefix",
        "faceResidueEquivSimpleFaceDivisor",
    ]
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--technical-record", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=ROOT / "source-inventory.json")
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location(
        "homotopy_verifier", ROOT / "scripts/verify.py"
    )
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    require, read, sha = verifier.require, verifier.read, verifier.sha
    path = args.technical_record.resolve()
    technical = read(path)
    require(
        technical["ok"]
        and technical["inputs_unchanged"]
        and technical["mode"] == "technical",
        "Technical checkpoint not passed",
    )
    require(
        all(
            technical[k] is False
            for k in [
                "accepted_homotopy_prerequisites",
                "actual_arrangement_asphericity_proved",
                "two_sided_nerve_homotopy_equivalence_proved",
                "full_landmark_5_proved",
                "full_theorem_1_8_proved",
            ]
        ),
        "Technical scope overstates results",
    )
    context, baseline, historical = verifier.accepted_context()
    _, bindings, _ = verifier.provider_bindings(True)
    require(
        bindings == technical["source_bindings"],
        "Source or review bindings changed after technical check",
    )
    coverage_path = path.parent / "project-coverage.json"
    require(
        sha(coverage_path) == technical["project_coverage_sha256"],
        "Technical coverage changed",
    )
    coverage = read(coverage_path)
    names = {
        name
        for values in coverage["audited_declarations_by_module"].values()
        for name in values
    }
    require(
        set(CRITICAL) <= names,
        "Critical declaration absent: " + repr(set(CRITICAL) - names),
    )
    tooling = {
        verifier.relative(p): sha(p)
        for p in [
            ROOT / "ProjectAudit.lean",
            ROOT / "scripts/verify.py",
            ROOT / "scripts/cache_prerequisites.py",
            BASE / ".github/workflows/homotopy.yml",
        ]
    }
    inventory = {
        **bindings,
        "kind": "frozen-homotopy-prerequisites-candidate-source-inventory",
        "accepted_homotopy_prerequisites": False,
        "full_landmark_5_proved": False,
        "full_theorem_1_8_proved": False,
        "actual_arrangement_asphericity_proved": False,
        "two_sided_nerve_homotopy_equivalence_proved": False,
        "acceptance_status": "Source-bound technical checkpoint passed; candidate frozen for final independent prerequisite reviews. Root acceptance and clean CI remain separate. All full-target flags remain false even after prerequisite acceptance.",
        "scope": "Actual original-complement compatible metric/local connector and concrete named metric ordered nerve with continuous forward/return maps and one-sided domination homotopy; actual homotopy-group injectivity/asphericity reduction conditional on actual nerve higher vanishing; tube/chamber intervals, genuine positive ribbon prefix lcm/gcd/greatest-simple/maximal-face tails, and actual geometric face-opposition and face-residue/divisor equivalence. No two-sided nerve homotopy equivalence or nerve contraction is proved.",
        "unproved_core": "Actual constructed-nerve or universal-cover higher-homotopy vanishing/contraction, the remaining higher Deligne bridge and full Theorem 1.8 remain unproved. Conditional reduction theorems do not discharge their geometric hypotheses.",
        "critical_declarations": sorted(CRITICAL),
        "audited_declarations_by_module": coverage["audited_declarations_by_module"],
        "compiled_declaration_occurrences_by_module": coverage[
            "compiled_declaration_occurrences_by_module"
        ],
        "compiled_duplicate_equivalences": coverage["compiled_duplicate_equivalences"],
        "external_canonical_declarations": coverage["external_canonical_declarations"],
        "physical_summary": coverage["summary"],
        "verification_source_sha256": tooling,
        "accepted_context_input_aggregate_sha256": verifier.aggregate(context),
        "accepted_context_verification_sha256": baseline,
        "historical_reviews_sha256": historical,
        "technical_verification_path": verifier.relative(path),
        "technical_verification_sha256": sha(path),
        "technical_verification_scope": {
            "mode": "technical",
            "old_accepted_context_input_count": len(context),
            "old_inputs_unchanged": True,
            "exact_replay_count": len(technical["exact_replays"]),
            "semantic_acceptance_claimed": False,
            "clean_skipped": technical["clean_skipped"],
            "clean_skip_reason": technical["clean_skip_reason"],
            "new_provider_canonical_declarations": technical[
                "provider_physical_summary"
            ]["canonical_declarations"],
            "new_provider_physical_occurrences": technical["provider_physical_summary"][
                "physical_occurrences"
            ],
        },
        "digest_convention": "SHA256 over exact file bytes; mapping aggregate is SHA256 of sorted compact JSON, as implemented by the frozen verifier.",
    }
    require(not args.output.exists(), "Refuse to overwrite frozen inventory")
    require(
        set(verifier.REVIEW_KEYS) <= inventory.keys(),
        "Missing final review binding key",
    )
    verifier.write(args.output, inventory)
    print(
        json.dumps(
            {
                "ok": True,
                "path": str(args.output),
                "sha256": sha(args.output),
                "physical_summary": coverage["summary"],
            }
        )
    )


if __name__ == "__main__":
    main()
