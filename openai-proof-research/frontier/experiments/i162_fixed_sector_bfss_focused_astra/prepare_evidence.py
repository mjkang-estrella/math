"""Build I162 receipts only. Never import or execute ancestor code."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / "frontier/sources/i162_fixed_sector_bfss_focused_astra"
REPORT = ROOT / "frontier/reviews/i162-fixed-sector-bfss-focused-astra.md"
PBASE = "frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Positive-eigenvalues-of-the-relative-SU-2-BFSS-Hamiltonian-October-5-2026"
PTEX = PBASE + "/build/positive-eigenvalues-relative-su2-bfss.tex"
PDFBASE = "frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside/preprints/Positive-eigenvalues-of-the-relative-SU-2-BFSS-Hamiltonian-October-5-2026"
PPDF = PDFBASE + "/positive-eigenvalues-relative-su2-bfss.pdf"
PX = PPDF + ".txt"
I155 = "frontier/sources/i155_fixed_sector_bfss_counting"
I158 = "frontier/sources/i158_fixed_sector_bfss_counting_r2"
OWN = str(SOURCE.relative_to(ROOT))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def row(rel):
    data = (ROOT / rel).read_bytes()
    return {"path": rel, "bytes": len(data), "sha256": sha(data)}


def save(name, value):
    with (SOURCE / name).open("x", encoding="utf-8") as output:
        json.dump(value, output, ensure_ascii=False, indent=2)
        output.write("\n")


def main():
    if (SOURCE / "seal.json").exists():
        raise RuntimeError("Sealed evidence cannot be prepared again")
    # Normalize only this agent's new report to the project's dollar math syntax.
    report = REPORT.read_text()
    REPORT.write_text(report.replace("\\(", "$").replace("\\)", "$"))
    reads = []

    def receipt(path, ranges, scope="fresh semantic read", origin=None):
        data = (ROOT / path).read_bytes()
        text = data.decode("utf-8")
        lines = text.split("\n")
        offsets = [0]
        for line in lines[:-1]:
            offsets.append(offsets[-1] + len(line) + 1)
        for first, last in ranges:
            last = min(last, len(lines))
            start = offsets[first - 1]
            end = offsets[last] if last < len(lines) else len(text)
            passage = text[start:end]
            reads.append({
                **row(path), "line_first": first, "line_last": last,
                "line_convention": "one-based LF split, inclusive; trailing LF retained",
                "character_start": start, "character_end": end,
                "characters_total": len(text), "raw_lf": text.count("\n"),
                "python_splitlines": len(text.splitlines()),
                "range_sha256": sha(passage.encode()),
                "ending": passage[-180:], "scope": scope,
                "status": "supplied and read without truncation in this bounded call",
                "origin": origin or path,
            })

    receipt("AGENTS.md", [(1, 30)], "instructions")
    receipt("sources/upstream.json", [(1, 20)], "pinned revision")
    receipt(OWN + "/README.md.snapshot", [(1, 17)], "acceptance standard", "frontier/iterations/README.md")
    receipt(OWN + "/TEN-FINDINGS.md.snapshot", [(1, 5)], "count and acceptance scope", "frontier/TEN-FINDINGS.md")
    receipt("sources/CONTENTS.md", [(6797, 6818)], "catalogue locator, not proof")
    receipt("sources/preprints-tree.json", [(59465, 59502)], "selected pinned path entries")
    receipt("frontier/iterations/i155-fixed-sector-bfss-counting.md", [(1, 220), (219, 268)])
    receipt("frontier/reviews/i158-fixed-sector-bfss-counting-r2.md", [(1, 240), (235, 290)],
            "historical incomplete report, challenged rather than authoritative")
    receipt(OWN + "/i158-brief.txt", [(1, 115), (116, 255), (256, 420), (421, 580), (581, 769)])
    receipt(OWN + "/i155-brief.txt", [(1, 130), (131, 255), (256, 385), (386, 662)])
    receipt(OWN + "/i158-other-fields.json", [(1, 100)], "all non-brief fields, decoded losslessly")
    receipt(OWN + "/i155-other-fields.json", [(1, 100)], "all non-brief fields, decoded losslessly")
    receipt(PTEX, [(1, 260), (261, 520), (521, 750), (751, 889)],
            "complete stipulated source, including all proof endings and bibliography")
    receipt(PX, [(1, 265), (266, 503)],
            "complete inherited PDF text freshly read; fraction-order ambiguity resolved by pinned TeX")
    receipt(PBASE + "/README.md", [(1, 100)], "source metadata")
    receipt(I155 + "/external/fnt.txt", [(1, 270), (271, 529)],
            "complete external v2 theorem/proof, approximation, slicing ending and bibliography")
    receipt(I155 + "/external/halpern.txt", [(1, 188)], "selected concrete overlap only, not full proof")
    for path in [
        I155 + "/new-bindings.json", I155 + "/external-operative-notes.json",
        I155 + "/failure-log.json",
        "frontier/sources/i153_many_body_spectral_discovery/manybody-bindings.json",
        I158 + "/failure-log.json", I158 + "/coverage.json", I158 + "/pending-obligations.json",
    ]:
        receipt(path, [(1, 2400)], "historical provenance/scope only, not inherited semantic reading")
    receipt(I158 + "/preseal-validation.json", [(1, 90), (91, 192)], "stale historical prevalidation")
    receipt(I158 + "/read-manifest.json", [(1, 110)], "partial inherited receipt inspection only")
    save("read-manifest.json", reads)
    save("pdf-reader-receipts.json", [
        {**row(PPDF), "pages": [1, 9], "status": "complete native PDF-reader parsed presentation",
         "scope": "Not an ancestor converter execution; fractional text order not authoritative over TeX"},
        {**row(I155 + "/external/fnt.pdf"), "pages": [1, 10],
         "status": "complete native PDF-reader parsed presentation",
         "scope": "v2 and full proof ending independently inspected"},
    ])
    tasks = []
    for n, rel in [
        (155, "frontier/iterations/iteration155-fixed-sector-bfss-counting-task.json"),
        (158, "frontier/iterations/iteration158-fixed-sector-bfss-counting-r2-task.json"),
    ]:
        data = json.loads((ROOT / rel).read_bytes())
        tasks.append({**row(rel), "iteration": n, "keys_in_order": list(data),
                      "brief_characters": len(data["brief"]),
                      "brief_view": OWN + f"/i{n}-brief.txt",
                      "other_fields_view": OWN + f"/i{n}-other-fields.json",
                      "scope": "All top-level fields and full decoded brief, no recursive expansion of unrelated historical prerequisites"})
    save("task-bindings.json", tasks)

    ledger_map = [
        ("README.md", "root-README.md.snapshot"),
        ("frontier/README.md", "frontier-README.md.snapshot"),
        ("frontier/TEN-FINDINGS.md", "TEN-FINDINGS.md.snapshot"),
        ("frontier/iterations/README.md", "README.md.snapshot"),
    ]
    save("live-ledgers.json", [
        {"live_path": live, "snapshot": row(OWN + "/" + snap),
         "scope": "Live drift allowed; immutable snapshot does not imply full semantic reading"}
        for live, snap in ledger_map
    ])
    upstream = json.loads((ROOT / "sources/upstream.json").read_bytes())
    tree = json.loads((ROOT / "sources/preprints-tree.json").read_bytes())
    indexed = {x["path"]: x for x in tree["tree"]}
    prefix = "preprints/Positive-eigenvalues-of-the-relative-SU-2-BFSS-Hamiltonian-October-5-2026/"
    pins = []
    for rel, local in [
        (prefix + "README.md", PBASE + "/README.md"),
        (prefix + "build/positive-eigenvalues-relative-su2-bfss.tex", PTEX),
        (prefix + "positive-eigenvalues-relative-su2-bfss.pdf", PPDF),
    ]:
        pins.append({"upstream_path": rel, "local": row(local), "git_sha": indexed[rel]["sha"],
                     "upstream_commit": upstream["commit"],
                     "pinned_url": "https://raw.githubusercontent.com/openai/math/" + upstream["commit"] + "/" + rel})
    save("pinned-sources.json", pins)
    save("source-bindings.json", {
        "P": {"pdf": row(PPDF), "text": row(PX), "tex": row(PTEX),
              "extraction": "inherited, no local re-extraction; text fresh-read, exact coefficient checked in TeX"},
        "FNT": {"pdf": row(I155 + "/external/fnt.pdf"), "text": row(I155 + "/external/fnt.txt"),
                "version": "1207.0680v2, 2012-11-06", "url": "https://arxiv.org/pdf/1207.0680v2",
                "acquisition": "existing I155 PDF/text binding, no new network retrieval"},
        "HS": {"pdf": row(I155 + "/external/halpern.pdf"), "text": row(I155 + "/external/halpern.txt"),
               "version": "hep-th/9712133v1, 1997-12-15",
               "scope": "only lines 1-188 fresh-read, selected overlap; no complete contribution review"},
    })
    save("failure-log.json", [
        {"kind": "truncated initial ledger displays",
         "detail": "Bare Read of iterations/README.md and TEN-FINDINGS.md stopped at the 60k display cap (294/1939 and 215/759 lines reported). No full-ledger semantic read claimed. Acceptance passages were recovered in bounded reads; initial snapshots retain the initial versions."},
        {"kind": "initial task field inspection",
         "detail": "Execute displayed non-brief values with a 1500-character cap. Full non-brief JSON views were subsequently read; both complete brief views were read in bounded LF ranges."},
        {"kind": "unsuccessful locators",
         "detail": "Globs under sources/ and an ignored corpus tree returned no TeX. The inherited search-domain.json locator identified the existing pinned TeX; it was then read completely. No retrieval or corpus copying followed."},
        {"kind": "fraction-order ambiguity",
         "detail": "PDF text presents the source fermion coefficient in ambiguous extraction order. Hash-matched original TeX explicitly says backslash-tfrac i2 in both statement and proof. S155 and I158 instead transcribe 2i. No upstream contradiction is inferred."},
        {"kind": "historical acquisition and execution failures",
         "detail": "I155 and I158 failure logs read as history. No historical failed retrieval is relabelled successful in I162. No fresh network retrieval was attempted. I158 has no seal and its stale prevalidation is not a sealed PASS."},
    ])
    save("scope.json", {
        "focused_gate_complete": True,
        "original_package_verdict": "FAIL",
        "failure": "S155 exact fermionic coefficient is 2i; source eq:potential is i/2",
        "core_statement": "Leading asymptotic proved in report with coefficient correction explicitly separate; not original proof PASS without repairs",
        "historical_i158_gate": "INCOMPLETE / UNRESOLVED, unchanged",
        "acceptance_count": 8, "contribution_gate": "not performed",
        "source_dependency": "Complete positive-eigenvalue manuscript; no threshold-state companion operation is used",
        "historical_exclusions": ["triangular critical-stability semantic re-audit", "Bose comparison re-audit", "adiabatic comparison re-audit", "recursive full-corpus traversal"],
        "new_finite_diagnostics_scope": "Exact arithmetic and source coefficient parsing only, after immutable validation; not universal proof",
        "no_children": True, "no_ancestor_execution": True,
        "no_corpus_copies": True, "no_staging_commits_publication": True,
    })
    baseline = json.loads((SOURCE / "ancestor-baseline.json").read_bytes())
    refs = {x["path"]: x for x in baseline}
    for rel in [
        "AGENTS.md", "sources/upstream.json", "sources/CONTENTS.md", "sources/preprints-tree.json",
        PTEX, PBASE + "/README.md", PPDF, PX,
        I155 + "/external/fnt.pdf", I155 + "/external/fnt.txt",
        I155 + "/external/halpern.pdf", I155 + "/external/halpern.txt",
        I155 + "/new-bindings.json", I155 + "/external-operative-notes.json", I155 + "/failure-log.json",
        "frontier/sources/i153_many_body_spectral_discovery/manybody-bindings.json",
    ]:
        refs[rel] = row(rel)
    save("references.json", [refs[k] for k in sorted(refs)])
    print(json.dumps({"prepared": True, "read_ranges": len(reads), "immutable_references": len(refs),
                      "ancestor_programs_executed": 0, "mathematical_diagnostics_run": 0}))


if __name__ == "__main__":
    main()
