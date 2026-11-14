#!/usr/bin/env python3
"""Prepare or verify the source-bound M5 prerequisites frontier without changing old contexts.

Default/--plan performs only static binding checks and prints the planned work.
--write-audit refreshes explicit audit imports/context arrays before root freeze.
--execute --mode technical builds/audits/replays but never claims M5 prerequisites acceptance.
--execute --mode final additionally requires root source-inventory.json and both
reviews/asphericity-prerequisites-{a,b}.json with accept-asphericity-prerequisites and exact bindings below.

Final inventory keys: project_source_sha256, configuration_sha256,
vendor_provenance_sha256, provider_active_source_sha256,
provider_original_source_sha256, provider_import_patch_sha256,
provider_assembly_sha256, provider_license_sha256, provider_audit_sha256,
provider_verification_source_sha256, provider_statement_reviews_sha256,
accepted_context_input_aggregate_sha256, verification_source_sha256 (all new
verification scripts/audit/workflow), accepted_asphericity_prerequisites=false
(candidate inventory; final reviews assert true), full_landmark_5_proved=false,
actual_arrangement_asphericity_proved=false,
full_theorem_1_8_proved=false, critical_declarations (nonempty list),
audited_declarations_by_module, compiled_declaration_occurrences_by_module,
compiled_duplicate_equivalences. Final review receipts bind all listed source/context/tooling
binding keys and all scope flags, plus source_inventory_sha256. No inventory is
written/frozen by this verifier; technical output includes observed coverage.
"""

from __future__ import annotations
import argparse, ast, datetime as dt, difflib, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT.parent
ALLOW = {"propext", "Classical.choice", "Quot.sound"}
BASELINE_ARCHIVE = (
    "docs/theorem18/landmarks/github-evidence/run-43573814974/archive-verification.json"
)
BASELINE_ARCHIVE_SHA256 = (
    "25e91b419126ee1fc96c2c06afe0cc1a790702e52c06c4edd27ce3b8b05607ba"
)
BASELINE_VERIFICATION = (
    "docs/theorem18/landmarks/github-evidence/run-43573814974/verification.json"
)
BASELINE_VERIFICATION_SHA256 = (
    "4fc286c0849d7bede42fab6d5702abd52bc98a42449e34ce10d3cc1b18c3ca83"
)

REVIEW_KEYS = [
    "project_source_sha256",
    "configuration_sha256",
    "vendor_provenance_sha256",
    "provider_active_source_sha256",
    "provider_original_source_sha256",
    "provider_import_patch_sha256",
    "provider_assembly_sha256",
    "provider_license_sha256",
    "provider_audit_sha256",
    "provider_verification_source_sha256",
    "provider_statement_reviews_sha256",
    "provider_reused_source_sha256",
    "provider_evidence_sha256",
    "accepted_context_input_aggregate_sha256",
    "verification_source_sha256",
]


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def aggregate(d):
    return hashlib.sha256(
        json.dumps(d, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def write(path, data):
    Path(path).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def relative(path):
    return str(Path(path).relative_to(BASE))


def source_map():
    return {
        relative(p): sha(p)
        for p in [
            ROOT / "ArtinAsphericity.lean",
            *sorted(ROOT.glob("ArtinAsphericity/**/*.lean")),
        ]
    }


def project_modules():
    return ["ArtinAsphericity"] + [
        str(p.relative_to(ROOT)).removesuffix(".lean").replace("/", ".")
        for p in sorted(ROOT.glob("ArtinAsphericity/**/*.lean"))
    ]


def aggregate_import_closure(modules):
    """Source-level check that the final public aggregate reaches every leaf."""
    expected = set(modules)
    reached = set()
    pending = ["ArtinAsphericity"]
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        source = ROOT / (module.replace(".", "/") + ".lean")
        for imports in re.findall(
            r"^(?:(?:public|meta)\s+)*import(?:\s+all)?\s+([^\n]+)",
            source.read_text(),
            re.MULTILINE,
        ):
            for imported in imports.split():
                if imported.startswith("--"):
                    break
                if imported in expected and imported not in reached:
                    pending.append(imported)
    return sorted(reached)


def config_map():
    return {
        relative(ROOT / p): sha(ROOT / p)
        for p in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]
    }


def accepted_context():
    archive_path = BASE / BASELINE_ARCHIVE
    verification_path = BASE / BASELINE_VERIFICATION
    require(
        sha(archive_path) == BASELINE_ARCHIVE_SHA256,
        "Changed accepted M4 archive verification",
    )
    require(
        sha(verification_path) == BASELINE_VERIFICATION_SHA256,
        "Changed accepted M4 final CI record",
    )
    archive, verification = read(archive_path), read(verification_path)
    require(
        archive["ok"] is True
        and verification["ok"] is True
        and verification["mode"] == "final",
        "M4 context verification failed",
    )
    require(
        archive["source_commit"]
        == verification["repository_head"]
        == "e7703926f3e486c0fca3a0fe292ab56d6411c248",
        "Accepted M4 source commit differs",
    )
    require(
        archive["full_landmark_4_proved"] is True
        and archive["full_theorem_1_8_proved"] is False,
        "Accepted M4 context scope differs",
    )
    context = archive["checked_source_sha256"]
    require(
        len(context) == archive["current_source_input_count"] == 996,
        "Accepted M4 source inventory is not 996 inputs",
    )
    for path, digest in context.items():
        require(
            (BASE / path).is_file() and sha(BASE / path) == digest,
            "Changed accepted 996 input: " + path,
        )
    reviews = {}
    for key in [
        "historical_reviews_sha256",
        "provider_statement_reviews_sha256",
        "project_statement_reviews_sha256",
    ]:
        for path, digest in verification.get(key, {}).items():
            require(
                path not in reviews or reviews[path] == digest,
                "Conflicting historical review hash: " + path,
            )
            require(sha(BASE / path) == digest, "Changed accepted review: " + path)
            reviews[path] = digest
    return (
        context,
        {
            BASELINE_ARCHIVE: BASELINE_ARCHIVE_SHA256,
            BASELINE_VERIFICATION: BASELINE_VERIFICATION_SHA256,
        },
        reviews,
    )


def provider_bindings(require_reviews=True):
    provenance_path = ROOT / "vendor/provenance.json"
    p = read(provenance_path)
    require(
        p["upstream_sha"] == "62bbc0596dc3539d488232e4e924a338548ea0a9",
        "Wrong TauCeti pin",
    )
    require(
        len(p["files"]) == len(p["topological_order"]) == 11
        and {f["module"] for f in p["files"]} == set(p["topological_order"])
        and all(
            m.startswith("ArtinAsphericityVendor.") for m in p["topological_order"]
        ),
        "Wrong complete-module provider cohort",
    )
    require(p["required_declarations"], "Provider endpoints missing")
    require(
        all(
            p[k] is False
            for k in [
                "full_landmark_5_proved",
                "full_theorem_1_8_proved",
                "actual_arrangement_asphericity_proved",
            ]
        ),
        "Provider provenance overstates scope",
    )
    recipe = read(ROOT / "vendor" / p["assembly_recipe"])
    relocations = recipe["module_relocations"]
    require(
        relocations == {f["upstream_module"]: f["module"] for f in p["files"]},
        "Provider import-relocation inventory differs",
    )
    active, original, patches = {}, {}, {}
    for f in p["files"]:
        for dest, path, key in [
            (active, ROOT / "vendor" / f["path"], "active_sha256"),
            (original, ROOT / "vendor" / f["original_path"], "upstream_sha256"),
            (patches, ROOT / "vendor" / f["patch_path"], "patch_sha256"),
        ]:
            require(sha(path) == f[key], "Provider byte mismatch: " + str(path))
            dest[relative(path)] = sha(path)
        require(
            f["selected_blocks"] == []
            and f["proofs_hypotheses_namespaces_unchanged"] is True,
            "Provider is not an unchanged whole-module relocation",
        )
        old = (ROOT / "vendor" / f["original_path"]).read_text()

        def relocate_import(match):
            return match[1] + " ".join(
                relocations.get(token, token) for token in match[2].split()
            )

        new = re.sub(
            r"^((?:(?:public|meta)\s+)*import\s+)([^\n]+)",
            relocate_import,
            old,
            flags=re.M,
        )
        require(
            (ROOT / "vendor" / f["path"]).read_bytes() == new.encode(),
            "Provider differs beyond import relocation: " + f["module"],
        )
        diff = "".join(
            difflib.unified_diff(
                old.splitlines(keepends=True),
                new.splitlines(keepends=True),
                fromfile=f["upstream_path"],
                tofile=f["path"],
            )
        )
        require(
            (ROOT / "vendor" / f["patch_path"]).read_bytes() == diff.encode(),
            "Provider diff is not exact: " + f["module"],
        )
    reused = {}
    for f in p["reused_pinned_dependencies"]:
        path = f["repository_relative_source"]
        require(
            f["equals_upstream_pinned_bytes"] is True
            and sha(BASE / path) == f["sha256"],
            "Changed reused provider source: " + path,
        )
        reused[path] = f["sha256"]
    require(len(reused) == 16, "Wrong reused provider closure")
    evidence = {
        relative(f): sha(f)
        for f in sorted((ROOT / "evidence/providers").rglob("*"))
        if f.is_file()
    }
    require(
        set(active)
        == {relative(f) for f in ROOT.glob("vendor/ArtinAsphericityVendor/**/*.lean")},
        "Extra/missing active provider",
    )
    require(
        set(original)
        == {relative(f) for f in ROOT.glob("vendor/upstream-original/**/*.lean.txt")},
        "Extra/missing full upstream originals",
    )
    require(
        set(patches) == {relative(f) for f in ROOT.glob("vendor/patches/**/*.patch")},
        "Extra/missing provider patch",
    )
    assembly = {
        relative(ROOT / p["assembly_script"]): p["assembly_script_sha256"],
        relative(ROOT / "vendor" / p["assembly_recipe"]): p["assembly_recipe_sha256"],
    }
    for path, digest in assembly.items():
        require(
            sha(BASE / path) == digest,
            "Changed provider assembly source/recipe: " + path,
        )
    license_path = ROOT / "vendor" / p["license"]["path"]
    require(sha(license_path) == p["license"]["sha256"], "Provider license changed")
    review_refs = {}
    accepted = True
    for label in ["a", "b"]:
        file = ROOT / "reviews" / f"providers-{label}.json"
        if not file.is_file():
            accepted = False
            require(not require_reviews, "Provider semantic review pending: " + label)
            continue
        review = read(file)
        require(
            review["verdict"] == "accept-supplier-cohort"
            and review["model"] == "gpt-6.1-sol"
            and review["reasoning_effort"] == "high",
            "Provider review not accepted",
        )
        require(
            review["full_landmark_5_proved"] is False
            and review["full_theorem_1_8_proved"] is False
            and review["actual_arrangement_asphericity_proved"] is False
            and review.get("accepted_asphericity_prerequisites", False) is False,
            "Provider review overstates scope",
        )
        require(
            review["vendor_provenance_sha256"] == sha(provenance_path),
            "Stale provider review provenance",
        )
        require(
            review["provider_source_sha256"] == active
            and review["provider_original_source_sha256"] == original,
            "Stale provider review source bytes",
        )
        require(
            review.get(
                "provider_import_patch_sha256", review.get("provider_patch_sha256")
            )
            == patches,
            "Stale provider review patches",
        )
        require(
            review["provider_assembly_sha256"] == assembly,
            "Stale provider review assembly/recipe",
        )
        require(
            review["configuration_sha256"] == config_map(),
            "Changed provider-reviewed package configuration",
        )
        require(
            review["provider_audit_sha256"] == sha(ROOT / "ProviderAudit.lean"),
            "Changed reviewed provider audit",
        )
        require(
            review.get(
                "provider_reused_source_sha256",
                review.get("reused_provider_source_sha256"),
            )
            == reused,
            "Stale reused provider closure review",
        )
        authoritative = read(ROOT / "evidence/providers/verification.json")
        reviewed_paths = {
            relative(f) for f in (ROOT / "evidence/providers").glob("*") if f.is_file()
        }
        for item in authoritative["records"].values():
            require(
                sha(ROOT / item["record"]) == item["sha256"],
                "Changed authoritative provider command record",
            )
            reviewed_paths.update(
                relative(f)
                for f in (ROOT / item["record"]).parent.rglob("*")
                if f.is_file()
            )
        require(
            review["evidence_sha256"]
            == {name: evidence[name] for name in reviewed_paths},
            "Incomplete authoritative provider evidence review",
        )
        for key in [
            "application_source_sha256",
            "evidence_sha256",
            "verification_scripts_sha256",
            "accepted_context_input_sha256",
        ]:
            for name, digest in review.get(key, {}).items():
                require(
                    sha(BASE / name) == digest,
                    "Changed provider-reviewed evidence/context: " + name,
                )
        review_refs[relative(file)] = sha(file)
        review_refs[relative(file.with_suffix(".md"))] = sha(file.with_suffix(".md"))
    bindings = {
        "project_source_sha256": source_map(),
        "configuration_sha256": config_map(),
        "vendor_provenance_sha256": sha(provenance_path),
        "provider_active_source_sha256": active,
        "provider_original_source_sha256": original,
        "provider_import_patch_sha256": patches,
        "provider_assembly_sha256": assembly,
        "provider_license_sha256": sha(license_path),
        "provider_audit_sha256": sha(ROOT / "ProviderAudit.lean")
        if (ROOT / "ProviderAudit.lean").is_file()
        else None,
        "provider_verification_source_sha256": {
            relative(file): sha(file)
            for file in sorted((ROOT / "scripts/providers").glob("*.py"))
        },
        "provider_statement_reviews_sha256": review_refs,
        "provider_reused_source_sha256": reused,
        "provider_evidence_sha256": evidence,
    }
    p["semantic_reviews_accepted"] = accepted
    return p, bindings, review_refs


def known_context_modules(context, provider):
    result = {f["module"] for f in provider["files"]}
    for path in context:
        if not path.endswith(".lean"):
            continue
        for prefix in [
            "sequences/vendor/",
            "sequences/",
            "chambers/vendor/",
            "chambers/",
            "ribbons/vendor/",
            "landmarks/vendor/",
            "vendor/",
            "ribbons/",
            "landmarks/",
            "",
        ]:
            if prefix and not path.startswith(prefix):
                continue
            module = path[len(prefix) :].removesuffix(".lean").replace("/", ".")
            if module.startswith(
                (
                    "TauCeti.",
                    "OAI.",
                    "ArtinSequenceVendor.",
                    "ArtinSequences.",
                    "ArtinLandmarkVendor.",
                    "ArtinChamberVendor.",
                    "ArtinChambers.",
                    "ArtinNormalisers.",
                    "ArtinLandmarks.",
                    "ArtinRibbons.",
                )
            ):
                result.add(module)
                break
    return sorted(result)


def audit_text(modules, context):
    source = (ROOT / "ProjectAudit.lean").read_text()

    def replace(key, value):
        nonlocal source
        source = re.sub(
            r"(?<=-- BEGIN GENERATED "
            + key
            + r"\n).*?(?=-- END GENERATED "
            + key
            + r")",
            lambda _: value,
            source,
            flags=re.S,
        )

    replace("IMPORTS", "".join("import " + m + "\n" for m in modules))
    replace("EXPECTED", ",\n".join("    `" + m for m in modules) + "\n")
    replace("CONTEXT", ",\n".join("    `" + m for m in context) + "\n")
    return source


def final_bindings(inv, bindings, context_digest):
    tooling = {
        relative(p): sha(p)
        for p in [
            ROOT / "ProjectAudit.lean",
            Path(__file__),
            ROOT / "scripts/cache_prerequisites.py",
            BASE / ".github/workflows/asphericity.yml",
        ]
    }
    expected = {
        **bindings,
        "accepted_context_input_aggregate_sha256": context_digest,
        "verification_source_sha256": tooling,
    }
    for key, value in expected.items():
        require(inv[key] == value, "Changed final inventory binding: " + key)
    require(
        inv["accepted_asphericity_prerequisites"] is False
        and all(
            inv[k] is False
            for k in [
                "full_landmark_5_proved",
                "actual_arrangement_asphericity_proved",
                "full_theorem_1_8_proved",
            ]
        ),
        "Final candidate inventory overstates checkpoint scope",
    )
    require(
        inv.get("critical_declarations"),
        "Final inventory has no actual prerequisite endpoints",
    )
    refs = {}
    for label in ["a", "b"]:
        path = ROOT / "reviews" / f"asphericity-prerequisites-{label}.json"
        review = read(path)
        require(
            review["verdict"] == "accept-asphericity-prerequisites"
            and review["model"] == "gpt-6.1-sol"
            and review["reasoning_effort"] == "high",
            "Final project review not accepted",
        )
        require(
            review["accepted_asphericity_prerequisites"] is True
            and all(
                review[k] is False
                for k in [
                    "full_landmark_5_proved",
                    "actual_arrangement_asphericity_proved",
                    "full_theorem_1_8_proved",
                ]
            ),
            "Final project review scope differs",
        )
        for key in REVIEW_KEYS:
            require(
                review[key] == expected[key], "Stale final review: " + label + ":" + key
            )
        require(
            review["source_inventory_sha256"] == sha(ROOT / "source-inventory.json"),
            "Final review does not bind exact inventory",
        )
        refs[relative(path)] = sha(path)
        refs[relative(path.with_suffix(".md"))] = sha(path.with_suffix(".md"))
    return refs


def exact_replay_source():
    # Reuse the already accepted exact-module implementation of the pinned official
    # checker algorithm; extract its literal without executing the old Python script.
    tree = ast.parse((BASE / "ribbons/scripts/verify_project.py").read_text())
    return next(
        ast.literal_eval(n.value)
        for n in tree.body
        if isinstance(n, ast.Assign)
        and any(isinstance(t, ast.Name) and t.id == "EXACT_REPLAY" for t in n.targets)
    )


def parse_rows(text, prefix):
    return [
        json.loads(s[len(prefix) :]) for s in text.splitlines() if s.startswith(prefix)
    ]


def validate_project_audit(text, modules, known):
    decls = parse_rows(text, "ASPHERICITY_PROJECT_DECL_JSON ")
    physical = parse_rows(text, "ASPHERICITY_PROJECT_COMPILED_MODULE_JSON ")
    aliases = parse_rows(text, "ASPHERICITY_PROJECT_DUPLICATE_JSON ")
    external = parse_rows(text, "ASPHERICITY_CONTEXT_DECL_JSON ")
    summary = parse_rows(text, "ASPHERICITY_PROJECT_SUMMARY_JSON ")
    module_rows = parse_rows(text, "ASPHERICITY_PROJECT_MODULE_JSON ")
    require(
        decls and len({d["name"] for d in decls}) == len(decls),
        "Empty or duplicate canonical project audit",
    )
    require(
        len(summary) == 1
        and len(physical) == len(modules)
        and {r["module"] for r in physical} == set(modules),
        "Missing physical/module summary coverage",
    )
    require(
        len(module_rows) == len(modules)
        and {r["module"] for r in module_rows} == set(modules),
        "Missing module audit rows",
    )
    by = {m: [] for m in modules}
    names = {}
    ext = {}
    for r in decls:
        require(
            r["module"] in by and set(r["axioms"]) <= ALLOW,
            "Unknown project owner or forbidden axiom",
        )
        by[r["module"]].append(r["name"])
        names[r["name"]] = r["module"]
    for r in external:
        require(
            r["name"] not in names
            and r["name"] not in ext
            and set(r["axioms"]) <= ALLOW,
            "Unverified external canonical duplicate",
        )
        ext[r["name"]] = r["module"]
    duplicate_map = {}
    for r in aliases:
        require(
            r["physical_module"] in by
            and all(
                r[k] is True
                for k in [
                    "same_type",
                    "same_proof",
                    "same_universe_parameters",
                    "theorem_in_both",
                ]
            )
            and set(r["canonical_axioms"]) <= ALLOW,
            "Invalid physical theorem duplicate",
        )
        owner = r["canonical_module"]
        foundation = any(
            owner == pfx or owner.startswith(pfx + ".")
            for pfx in ["Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq"]
        )
        require(
            owner in by or owner in known or foundation,
            "Unknown canonical duplicate owner",
        )
        key = (r["physical_module"], r["name"])
        require(key not in duplicate_map, "Duplicate overlap certificate")
        require(
            names.get(r["name"], ext.get(r["name"])) == r["canonical_module"],
            "Duplicate lacks audited canonical owner",
        )
        require(
            r["canonical_owner_is_new_project"] == (r["canonical_module"] in by),
            "Canonical duplicate owner classification differs",
        )
        duplicate_map[key] = r
    compiled = {}
    for r in physical:
        m = r["module"]
        require(
            r["declarations"] == len(r["names"]) == len(set(r["names"])),
            "Malformed physical inventory",
        )
        require(
            bool(r["names"]) if m != "ArtinAsphericity" else not r["names"],
            "Scientific leaf empty or aggregate not import-only",
        )
        compiled[m] = sorted(r["names"])
        for name in r["names"]:
            require(
                names.get(name) == m or (m, name) in duplicate_map,
                "Physical declaration lacks canonical/equality coverage",
            )
    unique = {n for ns in compiled.values() for n in ns}
    require(
        unique == set(names) | set(ext), "Physical/canonical/context name sets differ"
    )
    total = sum(map(len, compiled.values()))
    s = summary[0]
    require(
        s["modules"] == len(modules)
        and s["canonical_project_declarations"] == len(decls)
        and s["external_canonical_names"] == len(ext)
        and s["physical_occurrences"] == total
        and s["distinct_physical_names"] == len(unique)
        and s["identical_theorem_duplicates"] == len(aliases)
        and total == len(decls) + len(aliases),
        "Physical count accounting differs",
    )
    require(
        s["canonical_axioms_checked"]
        and s["all_physical_type_value_universe_parameters_identical"],
        "Audit did not assert exact contents",
    )
    for row in module_rows:
        require(
            row["imported"] is True
            and row["declarations"] == len(by[row["module"]])
            and row["physical_declarations"] == len(compiled[row["module"]]),
            "Module counts differ",
        )
    return {
        "audited_declarations_by_module": {m: sorted(v) for m, v in by.items()},
        "compiled_declaration_occurrences_by_module": compiled,
        "compiled_duplicate_equivalences": sorted(
            aliases, key=lambda r: (r["physical_module"], r["name"])
        ),
        "external_canonical_declarations": external,
        "summary": s,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--write-audit", action="store_true")
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--mode", choices=["technical", "final"], default="technical")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    require(
        not (args.execute and (args.plan or args.write_audit)),
        "Execute must be separate from static preparation",
    )
    try:
        context, baseline_records, historical_reviews = accepted_context()
        provider, bindings, provider_reviews = provider_bindings(
            require_reviews=args.execute
        )
        modules = project_modules()
        known = known_context_modules(context, provider)
    except BaseException as error:
        if args.execute:
            failure = (
                args.output
                or ROOT
                / "evidence"
                / dt.datetime.now(dt.timezone.utc).strftime(
                    "asphericity-prerequisites-preflight-%Y%m%dT%H%M%SZ"
                )
            ).resolve()
            failure.mkdir(parents=True, exist_ok=False)
            write(
                failure / "verification.json",
                {
                    "kind": "source-bound-asphericity-prerequisites-verification",
                    "ok": False,
                    "status": "preflight-failed",
                    "mode": args.mode,
                    "argv": sys.argv,
                    "commands": [],
                    "full_landmark_5_proved": False,
                    "actual_arrangement_asphericity_proved": False,
                    "accepted_asphericity_prerequisites": False,
                    "full_theorem_1_8_proved": False,
                    "finished_at": utc(),
                    "error": f"{type(error).__name__}: {error}",
                    "verifier_sha256": sha(Path(__file__)),
                },
            )
        raise
    expected_audit = audit_text(modules, known)
    if args.write_audit:
        (ROOT / "ProjectAudit.lean").write_text(expected_audit)
    aggregate_closure = aggregate_import_closure(modules)
    inherited_supplier_targets = []
    for path in [
        BASE / "vendor/provenance.json",
        BASE / "vendor/theorem18-provenance.json",
        BASE / "landmarks/vendor/provenance.json",
        BASE / "ribbons/vendor/provenance.json",
        BASE / "chambers/vendor/provenance.json",
        BASE / "sequences/vendor/provenance.json",
    ]:
        cohort = read(path)
        heads = cohort.get(
            "roots",
            cohort.get(
                "root_modules",
                cohort.get("topological_order", cohort.get("modules", [])),
            ),
        )
        inherited_supplier_targets.extend(
            h if isinstance(h, str) else h["module"] for h in heads
        )
    old_roots = list(dict.fromkeys(inherited_supplier_targets))
    new_provider = provider["topological_order"]
    targets = list(dict.fromkeys([*modules, *new_provider, *old_roots]))
    plan = {
        "kind": "asphericity-prerequisites-verification-infrastructure-plan",
        "mode": args.mode,
        "execute": args.execute,
        "full_landmark_5_proved": False,
        "actual_arrangement_asphericity_proved": False,
        "accepted_asphericity_prerequisites": False,
        "full_theorem_1_8_proved": False,
        "project_modules": modules,
        "aggregate_import_closure": aggregate_closure,
        "aggregate_imports_all_project_modules": set(aggregate_closure) == set(modules),
        "new_provider_modules": new_provider,
        "explicit_build_targets": targets,
        "inherited_supplier_build_targets": old_roots,
        "accepted_historical_input_counts": [996],
        "provider_reviews_accepted": provider["semantic_reviews_accepted"],
        "unified_historical_source_context_count": len(context),
        "historical_review_count": len(historical_reviews),
        "accepted_context_input_aggregate_sha256": aggregate(context),
        "expected_audit_is_current": (ROOT / "ProjectAudit.lean").read_text()
        == expected_audit,
        "final_inventory_required_keys": REVIEW_KEYS
        + [
            "accepted_asphericity_prerequisites",
            "actual_arrangement_asphericity_proved",
            "full_landmark_5_proved",
            "full_theorem_1_8_proved",
            "critical_declarations",
            "audited_declarations_by_module",
            "compiled_declaration_occurrences_by_module",
            "compiled_duplicate_equivalences",
        ],
        "kernel_replay_scope": "Only each new M5 prerequisites project module/aggregate and the eleven new exact provider modules, one module per fresh process. Old404 accepted supplier modules and Mathlib are not freshly replayed.",
    }
    if not args.execute:
        print(json.dumps(plan, indent=2))
        return 0
    require(
        plan["expected_audit_is_current"],
        "Audit imports/context stale; run --write-audit before review freeze",
    )
    output = (
        args.output
        or ROOT
        / "evidence"
        / dt.datetime.now(dt.timezone.utc).strftime(
            "asphericity-prerequisites-%Y%m%dT%H%M%SZ"
        )
    ).resolve()
    output.mkdir(parents=True, exist_ok=False)
    (output / "logs").mkdir()
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    env.setdefault("LEAN_NUM_THREADS", "2")
    record = {
        **plan,
        "kind": "source-bound-asphericity-prerequisites-verification",
        "ok": False,
        "full_landmark_5_proved": False,
        "actual_arrangement_asphericity_proved": False,
        "accepted_asphericity_prerequisites": False,
        "semantic_acceptance_claimed": False,
        "started_at": utc(),
        "commands": [],
        "mode": args.mode,
        "repository_head": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=BASE, text=True
        ).strip(),
        "limitations": [
            "Bundled kernel relative to imported environments, not an independent kernel.",
            "Old accepted source bytes and reviews reused from archived successful evidence; no fresh replay of all old suppliers or mathlib.",
            "Technical mode never asserts main M5 prerequisites acceptance.",
        ],
    }
    frozen = {}
    compiled = {}

    def bind(path, expected=None):
        path = Path(path).resolve()
        h = sha(path)
        require(expected is None or h == expected, "Input hash mismatch: " + str(path))
        require(
            str(path) not in frozen or frozen[str(path)] == h,
            "Input changed while binding",
        )
        frozen[str(path)] = h

    def unchanged():
        for path, h in frozen.items():
            require(sha(path) == h, "Input changed during verification: " + path)

    def save():
        write(output / "verification.json", record)

    def run(label, argv):
        log = output / "logs" / (label + ".log")
        start = time.monotonic()
        print("Running:", label, flush=True)
        with log.open("wb") as stream:
            p = subprocess.run(
                argv, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT
            )
        row = {
            "label": label,
            "argv": argv,
            "cwd": str(ROOT),
            "exit_code": p.returncode,
            "log": str(log.relative_to(output)),
            "log_sha256": sha(log),
            "elapsed_seconds": round(time.monotonic() - start, 3),
        }
        record["commands"].append(row)
        save()
        require(p.returncode == 0, label + " failed; see " + str(log))
        return log.read_text()

    save()
    try:
        for mapping in [
            context,
            baseline_records,
            historical_reviews,
            bindings["project_source_sha256"],
            bindings["configuration_sha256"],
            bindings["provider_active_source_sha256"],
            bindings["provider_original_source_sha256"],
            bindings["provider_import_patch_sha256"],
            bindings["provider_assembly_sha256"],
            bindings["provider_verification_source_sha256"],
            bindings["provider_reused_source_sha256"],
            bindings["provider_evidence_sha256"],
            provider_reviews,
        ]:
            for path, h in mapping.items():
                bind(BASE / path, h)
        for path in [
            Path(__file__),
            ROOT / "scripts/cache_prerequisites.py",
            ROOT / "ProjectAudit.lean",
            ROOT / "ProviderAudit.lean",
            ROOT / "vendor/provenance.json",
            ROOT / "vendor" / provider["license"]["path"],
            BASE / ".github/workflows/asphericity.yml",
        ]:
            if path.exists():
                bind(path)
        record.update(
            {
                "accepted_context_verification_sha256": baseline_records,
                "accepted_context_input_sha256": context,
                "historical_reviews_sha256": historical_reviews,
                "provider_statement_reviews_sha256": provider_reviews,
                "source_bindings": bindings,
            }
        )
        inventory = None
        final_reviews = {}
        if args.mode == "final":
            require(
                plan["aggregate_imports_all_project_modules"],
                "Final root aggregate does not import every project module",
            )
            inventory = read(ROOT / "source-inventory.json")
            final_reviews = final_bindings(inventory, bindings, aggregate(context))
            bind(ROOT / "source-inventory.json")
            for path, h in final_reviews.items():
                bind(BASE / path, h)
            record["project_statement_reviews_sha256"] = final_reviews
        run("lean-version", ["lake", "env", "lean", "--version"])
        run("lake-version", ["lake", "--version"])
        revision = run(
            "mathlib-revision",
            ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
        )
        require(
            revision.strip() == provider["project_mathlib_revision"],
            "Wrong imported Mathlib revision",
        )
        require(
            not run(
                "mathlib-tracked-status",
                [
                    "git",
                    "-C",
                    ".lake/packages/mathlib",
                    "status",
                    "--porcelain",
                    "--untracked-files=no",
                ],
            ).strip(),
            "Tracked Mathlib changes",
        )
        for package in read(ROOT / "lake-manifest.json")["packages"]:
            if package["type"] != "git" or package["name"].strip("«»") == "mathlib":
                continue
            name = package["name"].strip("«»")
            directory = ".lake/packages/" + name
            actual = run(
                "pin-" + name, ["git", "-C", directory, "rev-parse", "HEAD"]
            ).strip()
            require(
                actual == package["rev"], "Actual dependency revision differs: " + name
            )
            require(
                not run(
                    "tracked-status-" + name,
                    [
                        "git",
                        "-C",
                        directory,
                        "status",
                        "--porcelain",
                        "--untracked-files=no",
                    ],
                ).strip(),
                "Tracked dependency changes: " + name,
            )
        run(
            "provider-extraction-reproducibility",
            ["python3", provider["assembly_script"], "--check"],
        )
        run("clean-new-package", ["lake", "clean", "artin-asphericity"])
        run("build-exact-frontier", ["lake", "build", *targets])
        unchanged()
        audit = run(
            "project-statements-axioms-physical",
            ["lake", "env", "lean", "ProjectAudit.lean"],
        )
        coverage = validate_project_audit(audit, modules, known)
        write(output / "project-coverage.json", coverage)
        record["project_coverage_sha256"] = sha(output / "project-coverage.json")
        if inventory:
            for key in [
                "audited_declarations_by_module",
                "compiled_declaration_occurrences_by_module",
                "compiled_duplicate_equivalences",
            ]:
                require(
                    coverage[key] == inventory[key],
                    "Frozen physical/declaration inventory differs: " + key,
                )
            require(
                set(inventory["critical_declarations"])
                <= {
                    n
                    for ns in coverage["audited_declarations_by_module"].values()
                    for n in ns
                },
                "Actual landmark endpoints absent from audited project declarations",
            )
        provider_text = run(
            "provider-statements-axioms-physical",
            ["lake", "env", "lean", "ProviderAudit.lean"],
        )
        providers = parse_rows(
            provider_text, "ASPHERICITY_PROVIDER_PHYSICAL_MODULE_JSON "
        )
        summary = parse_rows(
            provider_text, "ASPHERICITY_PROVIDER_PHYSICAL_SUMMARY_JSON "
        )
        require(
            len(providers) == len(new_provider) == 11
            and {r["module"] for r in providers} == set(new_provider)
            and len(summary) == 1,
            "Incomplete new provider cohort physical coverage",
        )
        recorded_provider = read(ROOT / "evidence/providers/coverage.json")
        expected_summary = recorded_provider["summary"]
        require(
            summary[0] == expected_summary
            and summary[0]["canonical_axioms_checked"]
            and summary[0]["all_physical_type_value_universe_parameters_identical"],
            "Actual provider canonical/physical coverage differs from reviewed evidence",
        )
        physical_counts = {
            m: len(v)
            for m, v in coverage["compiled_declaration_occurrences_by_module"].items()
        }
        for row in providers:
            require(
                row["declarations"] == len(row["names"]) == len(set(row["names"])),
                "Malformed provider physical inventory",
            )
            physical_counts[row["module"]] = row["declarations"]
        recorded_provider = read(ROOT / "evidence/providers/coverage.json")
        require(
            {r["module"]: sorted(r["names"]) for r in providers}
            == {
                r["module"]: sorted(r["names"])
                for r in recorded_provider["physical_modules"]
            },
            "New provider actual physical names differ from reviewed coverage",
        )
        record["provider_physical_summary"] = summary[0]
        # Bind exact project/provider object parts and actual dependency interfaces.
        for i, module in enumerate([*modules, *new_provider]):
            source = ROOT / (
                (module.replace(".", "/") + ".lean")
                if module in modules
                else "vendor/" + module.replace(".", "/") + ".lean"
            )
            text = run(f"deps-{i:03d}", ["lake", "env", "lean", "--deps", str(source)])
            paths = [
                Path(line) for line in text.splitlines() if line.endswith(".olean")
            ]
            paths.append(
                ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
            )
            for path in paths:
                if not path.is_absolute():
                    path = ROOT / path
                for part in [
                    path,
                    Path(str(path) + ".server"),
                    Path(str(path) + ".private"),
                ]:
                    if part.is_file():
                        compiled[str(part.resolve())] = sha(part)
                        bind(part)
        runner = output / "ExactReplay.lean"
        runner.write_text(exact_replay_source())
        bind(runner)
        prefix = run(
            "toolchain-prefix", ["lake", "env", "lean", "--print-prefix"]
        ).strip()
        checker_source = Path(prefix) / "src/lean/LeanChecker.lean"
        bind(checker_source)
        for tool in ["lean", "lake", "leanchecker"]:
            bind(Path(run("resolve-" + tool, ["lake", "env", "which", tool]).strip()))
        write(
            output / "inputs.json",
            {"source_and_records_sha256": frozen, "compiled_parts_sha256": compiled},
        )
        record["inputs_sha256"] = sha(output / "inputs.json")
        record["bound_input_count"] = len(frozen)
        save()
        unchanged()
        replays = []
        for i, module in enumerate([*modules, *new_provider]):
            text = run(
                f"replay-{i:03d}-{module}",
                ["lake", "env", "lean", "--run", str(runner), module],
            )
            rows = parse_rows(text, "EXACT_REPLAY_JSON ")
            require(
                len(rows) == 1
                and rows[0]["module"] == module
                and rows[0]["exact"] is True
                and rows[0]["kernel_replay_passed"] is True
                and rows[0]["declarations"] == physical_counts[module],
                "Exact replay differs from PHYSICAL declaration count: " + module,
            )
            replays.append(
                {
                    "module": module,
                    "physical_declarations_expected": physical_counts[module],
                    "result": rows[0],
                }
            )
            record["exact_replays"] = replays
            save()
        unchanged()
        require(
            source_map() == bindings["project_source_sha256"]
            and project_modules() == modules,
            "Project frontier changed",
        )
        require(
            provider_bindings(require_reviews=True)[1:] == (bindings, provider_reviews),
            "Provider/review bindings changed",
        )
        if inventory:
            require(
                final_bindings(inventory, bindings, aggregate(context))
                == final_reviews,
                "Final project reviews changed",
            )
        record.update(
            {
                "ok": True,
                "inputs_unchanged": True,
                "full_landmark_5_proved": False,
                "actual_arrangement_asphericity_proved": False,
                "accepted_asphericity_prerequisites": args.mode == "final",
                "semantic_acceptance_claimed": args.mode == "final",
            }
        )
    except BaseException as error:
        record["error"] = f"{type(error).__name__}: {error}"
        print(record["error"], file=sys.stderr)
    finally:
        record["finished_at"] = utc()
        save()
    return 0 if record["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
