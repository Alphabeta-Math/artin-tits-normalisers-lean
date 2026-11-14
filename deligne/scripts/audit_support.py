"""Physical declaration coverage parser adapted from the accepted homotopy observer."""
import datetime as dt, hashlib, json, re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT.parent
ALLOW={"propext","Classical.choice","Quot.sound"}

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

def aggregate_import_closure(modules):
    """Source-level check that the final public aggregate reaches every leaf."""
    expected = set(modules)
    reached = set()
    pending = ["ArtinDeligne"]
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

def parse_rows(text, prefix):
    return [
        json.loads(s[len(prefix) :]) for s in text.splitlines() if s.startswith(prefix)
    ]

def validate_project_audit(text, modules, known):
    decls = parse_rows(text, "DELIGNE_PROJECT_DECL_JSON ")
    physical = parse_rows(text, "DELIGNE_PROJECT_COMPILED_MODULE_JSON ")
    aliases = parse_rows(text, "DELIGNE_PROJECT_DUPLICATE_JSON ")
    external = parse_rows(text, "DELIGNE_CONTEXT_DECL_JSON ")
    summary = parse_rows(text, "DELIGNE_PROJECT_SUMMARY_JSON ")
    module_rows = parse_rows(text, "DELIGNE_PROJECT_MODULE_JSON ")
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
            bool(r["names"]) if m != "ArtinDeligne" else not r["names"],
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
