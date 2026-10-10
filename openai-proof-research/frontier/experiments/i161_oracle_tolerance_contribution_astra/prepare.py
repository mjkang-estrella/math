"""Freeze scoped I161 evidence, then stop before prevalidation and sealing.

This script reads ancestor data, never imports or executes ancestor programs.
It does not traverse the corpus; scan.py already did the one preparation scan.
All output is exclusive-create and confined to the I161 source directory.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SOURCE = "frontier/sources/i161_oracle_tolerance_contribution_astra"
EXPERIMENT = "frontier/experiments/i161_oracle_tolerance_contribution_astra"
REPORT = "frontier/reviews/i161-oracle-tolerance-contribution-astra.md"
OUT = ROOT / SOURCE
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
CORPUS = "frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/"
SAMPLING = CORPUS + (
    "Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-"
    "September-26-2026/build/sections/"
)
P154 = "frontier/sources/i154_dimension_independent_oracle_tolerance/primary/"
P152 = "frontier/sources/i152_algorithmic_sampling_reconstruction_discovery/primary/"


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def dump(name, obj):
    with (OUT / name).open("x", encoding="utf-8") as handle:
        json.dump(obj, handle, ensure_ascii=False, indent=2, sort_keys=True)
        handle.write("\n")


def main():
    bindings = {}
    reads = []

    def bind(path, role):
        raw = (ROOT / path).read_bytes()
        if path not in bindings:
            bindings[path] = {
                "path": path, "sha256": digest(raw), "bytes": len(raw), "roles": []
            }
        if role not in bindings[path]["roles"]:
            bindings[path]["roles"].append(role)
        return raw

    def read(path, ranges, scope, phase="I161 session, including pre-compaction segment"):
        raw = bind(path, "fresh semantic read")
        lines = raw.decode("utf-8").split("\n")
        if ranges == "full":
            ranges = [[1, len(lines)]]
        passages = []
        for lo, hi in ranges:
            assert 1 <= lo <= hi <= len(lines), (path, lo, hi, len(lines))
            # Deliberately LF, not splitlines: PDF form feeds stay inside lines.
            text = "\n".join(lines[lo - 1:hi]).encode("utf-8")
            passages.append({"first": lo, "last": hi, "sha256": digest(text)})
        reads.append({"path": path, "passages": passages, "scope": scope, "phase": phase})

    for path in ["AGENTS.md", "sources/upstream.json"]:
        read(path, "full", "Controlling instructions/pin, complete")
    read("sources/CONTENTS.md", [[1, 100], [3334, 3343]],
         "Catalogue opening and sampling-family keyword passage, not full catalogue")

    # Original records are immutable bytes. Only I159/I160 complete brief reads
    # and scalar fields are credited; older embedded context is not a new audit.
    fields = []
    for number in [152, 154, 157, 159, 160, 161]:
        candidates = list((ROOT / "frontier/iterations").glob(f"iteration{number}-*task.json"))
        assert len(candidates) == 1
        path = str(candidates[0].relative_to(ROOT))
        raw = bind(path, "original task")
        task = json.loads(raw)
        item = {
            "path": path, "sha256": digest(raw),
            "nonbrief_fields": {k: v for k, v in task.items() if k != "brief"},
            "brief_sha256": digest(task["brief"].encode("utf-8")),
            "coverage": "Older historical byte binding; embedded material read where present in controlling briefs",
        }
        if number in (159, 160):
            decoded = SOURCE + f"/task{number}-decoded.txt"
            assert (ROOT / decoded).read_bytes() == task["brief"].encode("utf-8")
            item["decoded"] = decoded
            item["coverage"] = "Every brief character read in bounded displays; all other fields separately displayed"
            read(decoded, "full", item["coverage"])
        if number == 161:
            item["coverage"] = "All JSON fields read directly; dispatch-summary status preserved"
            read(path, "full", item["coverage"], "post-compaction continuation")
        fields.append(item)
    dump("task-fields.json", fields)

    for path in [
        "frontier/iterations/i152-algorithmic-sampling-reconstruction-discovery.md",
        "frontier/iterations/i154-dimension-independent-oracle-tolerance.md",
        "frontier/reviews/i157-dimension-independent-oracle-tolerance-r2.md",
        "frontier/reviews/i159-oracle-tolerance-focused-r3.md",
    ]:
        read(path, "full", "Original report/review read completely; scoped history, not a new audit of unrelated claims")

    for name in ["introduction", "preliminaries", "jets", "divergence",
                 "centering", "numerics", "implementation", "sampling"]:
        read(SAMPLING + name + ".tex", "full",
             "Complete upper-bound source file through ending, read in bounded displays")

    for name, ranges, scope in [
        ("shifted1", [[270, 639]],
         "Gaussian KL/chain rule; Theorems 3.1/3.2 and proof endings; Remark 3.4; Lemma 3.6/Theorem 3.7; not entire paper"),
        ("shifted3", [[480, 919]],
         "Preliminaries and full section 3.1 proof; next-section opening; not entire paper"),
        ("shifted3-journal", [[590, 1029]],
         "Full section 3.1 through proof ending and adjacent preliminaries/section 3.2 opening; not general-L appendix"),
        ("inexact", [[420, 569], [852, 1086], [1555, 1699], [1838, 1902]],
         "Condition N/Theorem 4; fundamental coupling, Theorem 4 proof and required Lemmas 2-4/7 endings; not entire paper"),
        ("cloud", [[1, 205]],
         "Header, introduction and complete Theorem 1.1 statement; likelihood-correction proof NOT read"),
    ]:
        read(P154 + name + ".txt", ranges, scope)
        bind(P154 + name + ".pdf", "existing primary PDF, reused without extraction")
    read(P152 + "picard.txt",
         [[1, 215], [1080, 1191], [1364, 1463], [2970, 3121], [3162, 3666]],
         "Introduction; Lemma 4.10/4.11 and C.3 proof ending; main Theorem 1.1 assembly; full Appendices D/E and references. Not whole companion chain.")
    read(P152 + "stochastic.txt", [[1, 215], [237, 389], [1181, 1305]],
         "Definitions/assumptions; FORS construction; Theorem 3.3 proof through ending 1268; start of C.1 lemma. Later technical/proximal proofs NOT newly read.")
    for name in ["picard", "stochastic"]:
        bind(P152 + name + ".pdf", "existing primary PDF, reused without extraction")

    companions = [
        ("Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026",
         "01-information-and-densities.tex", "full",
         "Complete information/density section, all proof endings"),
        ("Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026",
         "05-hybrids.tex", "full", "Complete hybrid section, all proof endings"),
        ("Conditional-information-under-deterministic-coordinate-sweeps-September-26-2026",
         "13-forest.tex", [[1, 115]],
         "Actual permutation model, entropy statement and adaptive-query occurrence; proof remainder NOT read"),
        ("A-dimension-free-logarithmic-Sobolev-inequality-for-subgaussian-log-concave-measures-September-23-2026",
         "01-introduction.tex", [[1, 170]],
         "LSI theorem/transport corollary and introductory comparisons; whole proof NOT read"),
        ("Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026",
         "01-model-information.tex", [[1, 204]],
         "Actual bit-state model, Borel-rule lemma and proof, entropy conventions; remainder NOT read"),
    ]
    for family, filename, ranges, scope in companions:
        read(CORPUS + family + "/build/sections/" + filename, ranges, scope,
             "post-compaction continuation")

    # Historical snapshots do not drift with live ledgers. Their bytes are reused,
    # not claimed to be the exact earlier live display snapshots.
    snap_path = "frontier/sources/i159_oracle_tolerance_focused_r3/snapshots.json"
    snapshots = json.loads(bind(snap_path, "historical ledger snapshot provenance"))
    for row in snapshots:
        assert digest(bind(row["snapshot"], "historical ledger snapshot, not fresh full-read credit")) == row["sha256"]
    dump("ledger-coverage.json", {
        "historical_snapshots": snapshots,
        "fresh_live_displays": [
            {"path": "frontier/TEN-FINDINGS.md", "LF_ranges": [[1, 759]],
             "note": "Session display coverage after recovery; later additions not read. Live bytes not immutable bindings."},
            {"path": "frontier/iterations/README.md", "LF_ranges": [[1, 180]],
             "note": "Session opening display; live bytes not immutable bindings."}
        ],
        "limit": "Historical snapshots are immutable reference context, not represented as fresh snapshots of those live displays."
    })
    for name in ["parent152-review.json", "parent154-review.json", "parent157-review.json"]:
        bind("frontier/sources/i159_oracle_tolerance_focused_r3/" + name,
             "historical parent response bytes; semantic context occurs in decoded controlling briefs")

    map_path = "frontier/sources/i160_oracle_tolerance_contribution_r4/corpus.json"
    mapping = json.loads(bind(map_path, "inherited flat map, freshly audited by scan.py"))
    for key in ["tree_path", "domain_path"]:
        bind(mapping[key], "original-position domain")
    bind("frontier/sources/i160_oracle_tolerance_contribution_r4/read-log.json",
         "inherited read log, NOT fresh read credit")
    bind("frontier/sources/i160_oracle_tolerance_contribution_r4/primary/retrieval.json",
         "inherited retrieval provenance, NOT fresh retrieval credit")

    dump("read-log.json", {
        "convention": "UTF-8 LF split; 1-based inclusive ranges; passage hash joins selected lines with LF, no synthetic trailing LF",
        "credit": "Actual semantic displays in this I161 session. Pre-compaction ranges retained by the session summary, not inferred from ancestor read logs.",
        "reads": reads
    })
    dump("bindings.json", {
        "pin": PIN,
        "files": [bindings[k] for k in sorted(bindings)],
        "corpus_map": map_path,
        "scope": "All corpus and historical-search domain bytes are additionally bound by the flat maps. No ancestor code execution or active I162 binding."
    })
    dump("review-status.json", {
        "task": "I161",
        "contribution": "TECHNICAL ONLY",
        "original_R154_proof": "I159 PASS without substantive repairs preserved",
        "new_mathematical_objection": None,
        "I157_broad_audit": "INCOMPLETE, historical unresolved verdict retained",
        "internal_reserve_blanket_independence": "FAIL retained",
        "I160": "Provider-interrupted preparation only; no inherited completed verdict",
        "accepted_findings": 8,
        "acceptance_edits": False,
        "remaining_limits": [
            "No worldwide-priority or exhaustive absence certification",
            "No common tolerance for all epsilon, bit complexity, or arbitrary-accuracy result",
            "Search-only Paulin-Whalley lead not used as a premise",
            "Unrelated historical recursive audits remain incomplete"
        ]
    })
    owned = []
    paths = [ROOT / REPORT]
    for folder in [SOURCE, EXPERIMENT]:
        paths.extend(p for p in (ROOT / folder).rglob("*") if p.is_file())
    for path in paths:
        rel = str(path.relative_to(ROOT))
        assert "__pycache__" not in rel
        if rel in [SOURCE + "/inventory.json", SOURCE + "/seal.json"]:
            continue
        raw = path.read_bytes()
        owned.append({"path": rel, "bytes": len(raw), "sha256": digest(raw)})
    owned.sort(key=lambda item: item["path"])
    assert len(owned) == len({r["path"] for r in owned})
    dump("inventory.json", {
        "schema": 1,
        "exclusions": [SOURCE + "/inventory.json", SOURCE + "/seal.json"],
        "files": owned,
        "rule": "One canonical owned inventory. Seal binds this inventory; inventory binds every other owned file. No resealing."
    })
    print(f"Prepared {len(bindings)} direct bindings, {len(reads)} read records, {len(owned)} owned files. NOT SEALED.")


if __name__ == "__main__":
    main()
