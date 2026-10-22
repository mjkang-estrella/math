#!/usr/bin/env python3
"""Compose the Arithmetic158 brief from the Arithmetic157 brief and write the
Source059 navigation records for the Arithmetic157 parent intake."""
import datetime
import hashlib
import json
import os

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROJ = os.path.dirname(os.path.dirname(os.path.dirname(C)))
HERE = os.path.dirname(os.path.abspath(__file__))
PRIV = os.path.join(HERE, "private")
os.makedirs(PRIV, exist_ok=True)
NOW = datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha(b):
    return hashlib.sha256(b).hexdigest()


# --- Source059 catalogue body and navigation -------------------------------
EXT = (105150, 106786)
with open(os.path.join(PROJ, "sources/CONTENTS.md"), "rb") as f:
    f.seek(EXT[0])
    probe = f.read(4000)
i060 = probe.find(b"**060. ")
assert i060 == EXT[1] - EXT[0], i060
body = probe[:i060]
nxt = probe[i060:]
assert body.startswith(b"**059. Counterexamples to Zariski\xe2\x80\x99s multiplicity conjecture.**")
assert nxt.startswith(b"**060. ")
assert b"lean/docs" not in body
BODY_SHA = sha(body)
with open(os.path.join(PRIV, "catalogue-059.md"), "wb") as f:
    f.write(body)
title060 = nxt[:nxt.find(b".**") + 3].decode()

nav_src = os.path.join(C, "discovery-arithmetic-r155-parent/private/title-navigation.json")
nav = json.load(open(nav_src))
assert nav["families_selected"]["058"] == "arithmetic157" and nav["next_header"]["family"] == 59
nav["numeric_range"] = [43, 60]
nav["titles"].append({"family": 59, "start": EXT[0], "title_end": None,
                      "raw": "**059. Counterexamples to Zariski\u2019s multiplicity conjecture.**",
                      "how": "header located earlier by one bounded 4000-byte seek after 103503; body [105150,106786) decoded once for arithmetic158 selection"})
nav["families_selected"]["059"] = "arithmetic158"
nav["next_header"] = {"family": 60, "start": EXT[1], "raw": title060,
                      "located_by": "one bounded 4000-byte seek after 105150 (title decoded in the same bounded window; end not located)"}
json.dump(nav, open(os.path.join(PRIV, "title-navigation.json"), "w"), indent=1)

# --- folder metadata --------------------------------------------------------
tree = json.load(open(os.path.join(PROJ, "sources/preprints-tree.json")))["tree"]
assert len(tree) == 13223
F1 = "preprints/Ambiently-homeomorphic-isolated-hypersurfaces-of-multiplicities-two-and-three-September-24-2026/"
F2 = "preprints/Ambiently-homeomorphic-isolated-hypersurface-germs-in-C4-with-multiplicities-four-and-five-September-27-2026/"
links = [l for l in body.decode().split("](preprints/")[1:]]
assert len(links) == 2 and links[0].startswith(F1[len("preprints/"):]) and links[1].startswith(F2[len("preprints/"):])
fam1 = [e for e in tree if e["path"].startswith(F1)]
fam2 = [e for e in tree if e["path"].startswith(F2)]
b1 = [e for e in fam1 if e["type"] == "blob"]
b2 = [e for e in fam2 if e["type"] == "blob"]
assert (len(fam1), len(b1)) == (22, 16) and (len(fam2), len(b2)) == (18, 15), (len(fam1), len(b1), len(fam2), len(b2))
w1 = [e for e in b1 if e["path"] == F1 + "build/paper.tex"][0]
w2 = [e for e in b2 if e["path"] == F2 + "build/paper.tex"][0]
assert w1["size"] == 1014 and w1["sha"] == "47218dcfbc946c9ec1bcdef33e0599588a81f9bb"
assert w2["size"] == 903 and w2["sha"] == "719196090775ef43a214f6d2ba08870dd4045283"
ver = sorted(e["path"][len(F1):] for e in b1 if e["path"].startswith(F1 + "verification/"))
assert ver == ["verification/support/explicit-relation.json", "verification/support/supplied_finite_rank.py", "verification/validation/explicit_relation.py"]
others = [e["path"] for e in tree if "ambiently-homeomorphic" in e["path"].lower() and not (e["path"].startswith(F1.rstrip("/")) or e["path"].startswith(F2.rstrip("/")))]
assert not others, others
json.dump({
    "family": 59,
    "catalogue_extent": list(EXT),
    "catalogue_sha256": BODY_SHA,
    "next_header_confirmed": "%s at %d (title decoded in the same bounded window)" % (title060, EXT[1]),
    "folders": [F1.rstrip("/"), F2.rstrip("/")],
    "blobs_per_folder": [16, 15],
    "total_blobs": 31,
    "tree_entries": [22, 18],
    "candidate_top_level_tex": ["two-and-three: build/paper.tex (1014 B, blob 47218dcfbc946c9ec1bcdef33e0599588a81f9bb)",
                                "four-and-five: build/paper.tex (903 B, blob 719196090775ef43a214f6d2ba08870dd4045283)"],
    "verification_blobs_two_and_three": ver,
    "lean_docs_link": False,
    "parent_read_source_proofs": False,
}, open(os.path.join(PRIV, "source059-selection.json"), "w"), indent=1)

# --- brief --------------------------------------------------------------------
ET = os.path.join(C, "expanded-target-2026-10-17")
old = open(os.path.join(ET, "fresh-arithmetic-r157-brief.txt"), encoding="utf-8").read().split("\n")
assert len(old) == 78
new = list(old)
assert new[0].startswith("Arithmetic discovery r157")
new[0] = "Arithmetic discovery r158 — confirmed Zariski-multiplicity counterexample operative-proof discovery."
new[1] = "Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r158/."

a = new[9].index("The ORIGINAL INITIAL briefs")
b = new[9].index("Exact COMPLETED exceptions do not widen containing directories.") + len("Exact COMPLETED exceptions do not widen containing directories.")
new[9] = new[9][:a] + (
    "The ORIGINAL INITIAL brief of Structural191, dispatched together with this round, contains the literal prospective guard *arithmetic*r158* before any arithmetic158 body existed, and this brief contains *structural*r191* before any structural191 body exists. "
    "Structural191 (Source315, its author root and parent records) is the only current active peer: exclude the ENTIRE *structural*r191* namespace and every body/parent/brief/copy/derivative/status/activity alias. "
    "Arithmetic156 is COMPLETED and CLOSED whole-scope PASS/TECHNICAL with ZERO count (its author root, both review roots and parent records are no longer live): exclude the ENTIRE *arithmetic*r156* namespace from broad selection; no bodies admitted. "
    "Structural190, Structural189, Arithmetic157, Arithmetic155, Structural188, Structural187, Arithmetic154, Arithmetic153, Structural186, Arithmetic152, Arithmetic151 and Arithmetic150 are COMPLETED PREFREEZE/no nominee and parent-archived; exclude every structural190, structural189, arithmetic157, arithmetic155, structural188, structural187, arithmetic154, arithmetic153, structural186, arithmetic152, arithmetic151 and arithmetic150 namespace from broad selection; only the exact COMPLETED exceptions below are direct reads. "
    "Also exclude every full-path alias of a completed or live round that lacks the literal r (for example arithmetic151-stopped.json style status aliases, arithmetic15N*, structural19N*, analytic18N*) by installing the no-r wildcard twins of every listed guard before traversal. "
    "Own arithmetic158 namespace remains excluded from broad authored-history scans; own files usable. No peer body/status/activity/summary/finding may be inspected, inferred or used as premise. Do not inspect or steer peers to certify supplied isolation. This is prompt chronology, not OS/perfect isolation. Exact COMPLETED exceptions do not widen containing directories."
) + new[9][b:]

assert new[39].startswith("Catalogue access for THIS round")
new[39] = ("Catalogue access for THIS round, if needed at all: ONLY direct binary seek/read sources/CONTENTS.md[105150,106786), confirmed exact Source059 body. "
           "Parent reused numeric-header TITLE-ONLY43–59, located the 060 header by one bounded 4000-byte seek after 105150 and selected ONLY this family; parent has NOT read source theorem/proof bodies. The body links no Lean documentation page. "
           "No child catalogue scan, heading locator, read_text/readlines/whole read_bytes/decode or extra family. Full-tree metadata predicates use casefolded FULL paths. Selector failure is disclosed, never authorization for a wider span.")

assert new[41].startswith("Read these exact COMPLETED originals")
new[41] = (
    "Read these exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/: discovery-arithmetic-r157-parent/assessment.md; fresh-arithmetic-discovery-r157/packet/FINAL.md; fresh-arithmetic-discovery-r157/packet/notes/01-operative-comparison.md; fresh-arithmetic-discovery-r157/packet/notes/02-integrated-scaling-reduction.md; fresh-arithmetic-discovery-r157/packet/notes/03-admissible-returns-and-unpaid-operation.md; fresh-arithmetic-discovery-r157/packet/private/READING-ISOLATION.md. These completed inputs admit no containing namespace or status/activity access. "
    "Arithmetic157 remains PREFREEZE/no nominee: on Source058 (semialgebraic universal covers / bounded semialgebraic domains with compact quotient) it pays Stein holomorphic hulls supplying the analytic-disc continuity input without cocompactness, finite-volume orbit envelopes giving ordinary returns to the generic supported peak, closure of the source's forward/inverse scaling construction given an explicit compact-normalized interior anchor, the Siegel-domain/tube/Vey rotational-disc step and the Vey grading trace identity forcing transitivity; the good-point/moving-center multiple-scale normalization supplying the noncollapsed interior anchor with two-sided control for the full finite-volume scope remains unpaid, and its Kähler–Einstein bounded-domain scope is not this family. "
    "Structural190 (structural finite-precision elimination or global chain exchange with an a priori stabilization bound for cyclic lengths of finite p-group products unpaid), Structural189 (source-specific effectively represented all-orders chain contraction in the deformation-adic filtration unpaid), Arithmetic155 (geometric control of the low places spendable by negative small diagrams in generalized-canonical Kähler fourfold flip sequences unpaid), Structural188 (collapse-preserving lift c_S θ̃=θ c_j for every freely adjoined coherator operation unpaid), Structural187 (effective sampling constants/coordinate transfer or all-strata orbit-ideal lifting unpaid), Arithmetic154 (continuation of the quintic stability family through s=0 to the Gepner point unpaid), Arithmetic153 (geometric integrally marked gluing transport unpaid), Arithmetic152 (exact marked cancellation at the original exponent for b≥302 unpaid), Arithmetic151 (global holomorphic correction outside Calabi–Yau-base cases unpaid), Arithmetic150, Structural186 (uniform mixed overlap/attachment control across distinct extensions unpaid), Structural185, Arithmetic149/148, Structural184 and Analytic177 remain PREFREEZE/no nominee at their exact gaps. No retry/general impossibility. "
    "Arithmetic156 (Source057 root-stack fundamental-group isomorphism for the four-factor diagonal-quadric eightfold), Arithmetic147, S183N, S182P, Analytic161/T337A161 and T366A166 are whole-scope PASS/TECHNICAL, correctness conditions DISCHARGED, ZERO count; no bodies admitted or desired-grade retries. S176A remains correctness INCOMPLETE and contribution TECHNICAL conditional on full correctness, condition UNDISCHARGED; no necessary repair/counterexample established. T054L136 remains UNRESOLVED_FULL_SCOPE_REPAIR and NEEDS_REPAIR/INCOMPLETE. "
    "All older full targets/dispositions remain immutable, including every Zariski multiplicity/topological equivalence of hypersurface germs, Milnor fibration/link/Milnor number, embedded topological type, bi-Lipschitz/C¹/ambient homeomorphism invariance, Arnold corank/right equivalence, isolated hypersurface singularity, Brieskorn–Pham/exotic sphere, h-cobordism/surgery in singularity links, knot-theoretic link invariants and real/complex topology-of-singularities scope encountered in eligible ORIGINAL history."
)

assert new[43].startswith("Your ONE developed family is confirmed SOURCE058")
new[43] = ("Your ONE developed family is confirmed SOURCE059: COUNTEREXAMPLES TO ZARISKI'S MULTIPLICITY CONJECTURE. TWO canonical manuscript folders, THIRTY-ONE tree blobs: ambiently-homeomorphic-isolated-hypersurfaces-of-multiplicities-two-and-three (September-24; wrapper build/paper.tex of 1014 bytes, preamble, references.bib, one figure input, seven section inputs under build/sections, README, compiled PDF, and three verification objects under verification/: support/explicit-relation.json of 156782 bytes, support/supplied_finite_rank.py and validation/explicit_relation.py; sixteen blobs) and ambiently-homeomorphic-isolated-hypersurface-germs-in-C4-with-multiplicities-four-and-five (September-27; wrapper build/paper.tex of 903 bytes, preamble, references.bib, one figure input, nine numbered section inputs under build/sections, README, compiled PDF; fifteen blobs). "
           "Establish from the bodies what each wrapper includes, how the two manuscripts depend on one another (the catalogue presents a dimension-divisible-by-eight pair of multiplicities two and three with topologically right-equivalent defining germs answering Arnold's corank problem negatively for ambient topological equivalence, and a four-variable pair of multiplicities four and five), and what the verification objects actually compute and which stated step they support; never decide this from names. Parent infers nothing from filenames. Authenticate ALL thirty-one blobs. "
           "Read every wrapper, README and actual FULL headline statement, and read COMPLETELY the operative proof bodies of every manuscript your developed operation relies on, with ALL their operative includes/required companions, strongest actual primary versions and relevant operative ORIGINAL history mechanisms BEFORE extended deductions or author drafting; disclose exactly which sections of the remaining manuscript were not semantically read. Verification code may be read and rerun inside your own root only on authenticated copies; it is finite evidence for a stated step, not a proof and not a mathematical gate. "
           "Source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Validate new deductions/applicability, never audit source truth because it disproves Zariski's multiplicity conjecture.")

assert new[46].startswith("preprints/Semialgebraic-universal-covers")
new[46] = F1 + "build/paper.tex"
new[47] = "bytes1014; Git blob47218dcfbc946c9ec1bcdef33e0599588a81f9bb."
assert new[48].startswith("preprints/Symmetry-of-semialgebraic")
new[48] = F2 + "build/paper.tex"
new[49] = "bytes903; Git blob719196090775ef43a214f6d2ba08870dd4045283."

assert new[51].startswith("Follow actual nested includes")
new[51] = (
    "Follow actual nested includes/ancestors and complete-tree same-family objects of BOTH manuscripts, whose actual contents you must establish from the bodies; no guessed wrapper and no inference of a section's content from its filename. "
    "The source already proves, per catalogue: Zariski's multiplicity conjecture is false; there exist reduced holomorphic hypersurface germs that are ambiently homeomorphic but have different multiplicities; (i) two reduced hypersurface germs with isolated singularities in a common complex affine space of dimension divisible by eight, ambiently homeomorphic, of multiplicities two and three, whose defining function germs are topologically right equivalent, answering the embedded Zariski question negatively and Arnold's corank problem negatively for ambient topological equivalence; (ii) two reduced convergent holomorphic function germs in C^4 with isolated critical points and multiplicities four and five whose zero-set germs are ambiently homeomorphic. "
    "These headlines, the constructions, link/boundary, tube, collapse, lattice, filling and arithmetic steps as the bodies actually perform them, the classical Milnor fibration/link, h-cobordism/surgery, exotic-sphere and topological-manifold inputs as the bodies actually use them, and any compiled or scripted finite verifications are paid, not nominees. "
    "Read the actual mechanism (how the two germs are defined, how the ambient homeomorphism is constructed and where isolatedness, reducedness, the dimension restriction, the specific multiplicities and the complex structure are each used, how multiplicity and topological right equivalence are controlled, what the verification data certify and which classical results are inputs versus outputs), the exact definitions of ambient homeomorphism, multiplicity and topological right equivalence in each manuscript, and any limitation, non-uniqueness or open-case statements the sources themselves contain. "
    "Do NOT infer statements for other dimensions or multiplicity pairs beyond those stated, for non-isolated or non-reduced germs, for the non-embedded (abstract-homeomorphism) or C¹/bi-Lipschitz forms of the question, for plane curves or surfaces where classical positive results hold, for Lê's conjecture or Milnor-number invariance, for families, deformations or equisingularity statements, for real-analytic or algebraic-over-subfield versions, for Arnold's problem under other equivalences, or for finer structure of the homeomorphisms than stated, from the proved statements. Stipulate every source operation rather than rejecting the headline by older partial results."
)

assert new[53].startswith("Develop a DISTINCT")
new[53] = new[53].replace("source semialgebraic-cover/bounded-domain/factorization mechanisms", "source germ-construction/ambient-homeomorphism/multiplicity-control mechanisms")
new[53] = new[53].replace("routine boundary/coefficient/dimension substitutions, unsupported extension to non-normal, non-projective, merely definable, non-cocompact or intermediate-cover settings",
                          "routine coefficient/dimension/multiplicity substitutions, unsupported extension to non-isolated, non-reduced, abstract-homeomorphism, bi-Lipschitz, low-dimensional or deformation settings")
assert "germ-construction/ambient-homeomorphism" in new[53] and "non-isolated, non-reduced" in new[53]

text = "\n".join(new)
for bad in ["r157-brief", "SOURCE058", "103503", "105150)", "Semialgebraic-universal", "Symmetry-of-semialgebraic", "145b8ff0", "75578580", "18083", "11534", "TWENTY-THREE", "Kollár–Pardon", "lean/docs/058", "*arithmetic*r157* before", "Both are the current active peers", "fresh-arithmetic-discovery-r155/"]:
    assert bad not in text, bad
assert "fresh-arithmetic-discovery-r158/" in text and "[105150,106786)" in text and "*arithmetic*r158*" in text and "*structural*r191*" in text
out = os.path.join(ET, "fresh-arithmetic-r158-brief.txt")
assert not os.path.exists(out)
open(out, "w", encoding="utf-8").write(text)
raw = open(out, "rb").read()
BRIEF_SHA, BRIEF_BYTES = sha(raw), len(raw)

json.dump({
    "observed_utc": NOW,
    "before_arithmetic158_root_and_brief_dispatch": True,
    "live_peers_at_composition": "none running; Structural191 (Source315) is composed and dispatched in the same parent step and is the sole active peer",
    "mutual_guards": {"this_brief_contains": "*structural*r191* (supplement line, inherited) and the explicit peer-namespace exclusion",
                      "peer_brief_contains": "*arithmetic*r158* (supplement line, inherited) and the explicit peer-namespace exclusion"},
    "closed_round_excluded": {"Arithmetic156": "CLOSED PASS/TECHNICAL zero count; namespace excluded from broad selection; no bodies admitted"},
    "no_live_body_status_activity_or_findings_read": True,
    "completed_inputs_read_by_parent_before_brief": [
        "discovery-arithmetic-r157-parent/assessment.md (parent-authored)",
        "fresh-arithmetic-discovery-r157/packet/FINAL.md",
        "fresh-arithmetic-discovery-r157/packet/notes/00-feasibility-checkpoint.md",
        "fresh-arithmetic-discovery-r157/packet/notes/01-03 (large parts, at the r157 intake)",
    ],
    "limits": "Initial prompt chronology, not OS/perfect isolation.",
    "new_root_created_after_initial_guards_and_before_dispatch": True,
    "new_brief": {"path": "expanded-target-2026-10-17/fresh-arithmetic-r158-brief.txt", "sha256": BRIEF_SHA, "bytes": BRIEF_BYTES},
    "prospective_guard_supplement_in_brief": "carried: *arithmetic*r160*..r162*, *structural*r195*..r197*, *analytic*r187*..r189*; plus the no-r wildcard-twin instruction closing the alias admission disclosed by the completed Structural190 round",
    "completed_exceptions_granted": "r157 parent assessment, packet FINAL, notes/01-03 and packet/private/READING-ISOLATION.md; r155 exceptions withdrawn (unrelated flip-termination family)",
    "source059_preparation": {
        "one_family": True,
        "catalogue_extent": list(EXT),
        "catalogue_sha256": BODY_SHA,
        "next_header_located_by_one_bounded_4000_byte_seek": True,
        "title_only_navigation_range": [43, 60],
        "canonical_objects": 31,
        "canonical_folders": 2,
        "tree_entries": [22, 18],
        "lean_docs_link": False,
        "parent_read_source_proofs": False,
    },
}, open(os.path.join(HERE, "prospective-isolation-arithmetic158.json"), "w"), indent=1)

root = os.path.join(C, "fresh-arithmetic-discovery-r158")
os.mkdir(root)
print(json.dumps({"brief_sha256": BRIEF_SHA, "brief_bytes": BRIEF_BYTES, "root": root, "title060": title060, "body_sha256": BODY_SHA}))
