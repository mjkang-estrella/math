#!/usr/bin/env python3
"""Compose the Structural193 brief from the Structural192 brief and write the
Source317 navigation records for the Structural192 parent intake."""
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


# --- Source317 catalogue body and navigation -------------------------------
EXT = (539611, 540867)
with open(os.path.join(PROJ, "sources/CONTENTS.md"), "rb") as f:
    f.seek(EXT[0])
    body = f.read(EXT[1] - EXT[0])
    f.seek(EXT[1])
    nxt = f.read(4000)
assert body.startswith(b"**317. Thomason model structures in all strict higher dimensions.**")
assert nxt.startswith(b"**318. Chromatic splitting: filtrations and counterexamples.**")
i319 = nxt.find(b"**319. ")
assert i319 >= 0
assert body.count(b"lean/docs/") == 1 and b"(lean/docs/317.md)" in body  # this family links a Lean documentation page
BODY_SHA = sha(body)
assert BODY_SHA == "91568fbdee7b1ffead2fd2a53fb3dc634ae1f35e53e7b344c287352a0e5b586c"
with open(os.path.join(PRIV, "catalogue-317.md"), "wb") as f:
    f.write(body)

nav_src = os.path.join(C, "discovery-structural-r191-parent/private/title-navigation.json")
nav = json.load(open(nav_src))
assert nav["families_selected"][-1] == {"family": 316, "round": "structural192"}
assert nav["next_header"]["family"] == 317 and nav["next_header"]["start"] == EXT[0]
title319 = nxt[i319:nxt.find(b".**", i319) + 3].decode()
nav["numeric_range"] = [300, 319]
nav["titles"].append({"family": 319, "start": EXT[1] + i319,
                      "title_end": EXT[1] + i319 + len(title319.encode()),
                      "raw": title319})
nav["families_selected"].append({"family": 317, "round": "structural193"})
nav["next_header"] = {"family": 318, "start": EXT[1],
                      "located_by": "318 header located at the structural192 dispatch by one bounded 4000-byte seek after 539611; body [539611,540867) decoded once for structural193 selection; 319 header located by one bounded 4000-byte seek after 540867",
                      "incidental_display": "the bounded window after 540867 displayed the 318 title to the parent as navigation only; no source theorem/proof body was read and no family other than 317 was selected"}
json.dump(nav, open(os.path.join(PRIV, "title-navigation.json"), "w"), indent=1)

# --- folder metadata --------------------------------------------------------
tree = json.load(open(os.path.join(PROJ, "sources/preprints-tree.json")))["tree"]
assert len(tree) == 13223
PRE = "preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/"
assert body.decode().count("](preprints/") == 1 and PRE[len("preprints/"):] + "paper.pdf" in body.decode()
fam = [e for e in tree if e["path"].startswith(PRE)]
blobs = [e for e in fam if e["type"] == "blob"]
assert len(fam) == 15 and len(blobs) == 13, (len(fam), len(blobs))
wrap = [e for e in blobs if e["path"] == PRE + "build/paper.tex"][0]
assert wrap["size"] == 3804 and wrap["sha"] == "8c9f165f64359998bbd84da06247fea5920225f4"
WRAP_SHA = wrap["sha"]
names = sorted(e["path"][len(PRE):] for e in blobs)
assert names == ["README.md", "build/paper.tex", "build/references.bib", "build/sections/01-introduction.tex", "build/sections/02-foundations.tex",
                 "build/sections/03-relative-prisms.tex", "build/sections/04-labelled-pieces.tex", "build/sections/05-couniversality.tex",
                 "build/sections/06-subdivided-attachments.tex", "build/sections/07-model-structure.tex", "build/sections/08-method-context.tex",
                 "build/sections/09-presentability.tex", "paper.pdf"], names
others = [e["path"] for e in tree if "thomason" in e["path"].lower() and not e["path"].startswith(PRE.rstrip("/"))]
assert not others, others
json.dump({
    "family": 317,
    "catalogue_extent": list(EXT),
    "catalogue_sha256": BODY_SHA,
    "next_header_confirmed": "**318. Chromatic splitting: filtrations and counterexamples.** at 540867 (located earlier); 319 header at %d" % (EXT[1] + i319),
    "folders": [PRE.rstrip("/")],
    "blobs_per_folder": [13],
    "total_blobs": 13,
    "tree_entries": 15,
    "candidate_top_level_tex": ["build/paper.tex (3804 B, blob %s)" % WRAP_SHA],
    "blob_names_only": names,
    "lean_docs_link": "lean/docs/317.md (navigation outside the preprints tree)",
    "parent_read_source_proofs": False,
}, open(os.path.join(PRIV, "source317-selection.json"), "w"), indent=1)

# --- brief --------------------------------------------------------------------
ET = os.path.join(C, "expanded-target-2026-10-17")
old = open(os.path.join(ET, "fresh-structural-r192-brief.txt"), encoding="utf-8").read().split("\n")
assert len(old) == 76
new = list(old)
assert new[0].startswith("Structural discovery r192")
new[0] = "Structural discovery r193 — confirmed Thomason model structures in every strict higher dimension (Ara–Maltsiniotis conjecture) operative-proof discovery."
new[1] = "Write ONLY frontier/campaigns/2026-10-14/fresh-structural-discovery-r193/."

a = new[9].index("The ORIGINAL INITIAL brief of Arithmetic159")
b = new[9].index("Exact COMPLETED exceptions do not widen containing directories.") + len("Exact COMPLETED exceptions do not widen containing directories.")
new[9] = new[9][:a] + (
    "The ORIGINAL INITIAL brief of Arithmetic160, dispatched before this round, contains the literal prospective guard *structural*r193* before any structural193 body existed, and this brief contains *arithmetic*r160* while arithmetic160 is live. "
    "Arithmetic160 (Source062, its author root and parent records, including the progress-2026-10-22-owner-recovery parent directory) is the only current active peer: exclude the ENTIRE *arithmetic*r160* namespace, *owner-recovery* and every body/parent/brief/copy/derivative/status/activity alias. "
    "Arithmetic156 is COMPLETED and CLOSED whole-scope PASS/TECHNICAL with ZERO count (its author root, both review roots and parent records are no longer live): exclude the ENTIRE *arithmetic*r156* namespace from broad selection; no bodies admitted. "
    "Structural192, Arithmetic159, Structural191, Arithmetic158, Structural190, Structural189, Arithmetic157, Arithmetic155, Structural188, Structural187, Arithmetic154, Arithmetic153, Structural186, Arithmetic152, Arithmetic151 and Arithmetic150 are COMPLETED PREFREEZE/no nominee and parent-archived; exclude every structural192, arithmetic159, structural191, arithmetic158, structural190, structural189, arithmetic157, arithmetic155, structural188, structural187, arithmetic154, arithmetic153, structural186, arithmetic152, arithmetic151 and arithmetic150 namespace from broad selection; only the exact COMPLETED exceptions below are direct reads. "
    "Also exclude every full-path alias of a completed or live round that lacks the literal r (for example arithmetic151-stopped.json style status aliases, arithmetic15N*, arithmetic16N*, structural19N*, analytic18N*) by installing the no-r wildcard twins of every listed guard before traversal, and verify by an explicit policy comparison BEFORE traversal that every literal guard listed in this brief, including *k369r134-* and *t185r144-*, and its no-r twin is actually installed. "
    "Own structural193 namespace remains excluded from broad authored-history scans; own files usable. No peer body/status/activity/summary/finding may be inspected, inferred or used as premise. Do not inspect or steer peers to certify supplied isolation. This is prompt chronology, not OS/perfect isolation. Exact COMPLETED exceptions do not widen containing directories."
) + new[9][b:]

assert new[39].startswith("Catalogue access for THIS round")
new[39] = ("Catalogue access for THIS round, if needed at all: ONLY direct binary seek/read sources/CONTENTS.md[539611,540867), confirmed exact Source317 body. "
           "Parent reused numeric-header TITLE-ONLY300–318, located the 319 header by one bounded 4000-byte seek after 540867 (that window displayed the 318 title to the parent as navigation only) and selected ONLY this family; parent has NOT read source theorem/proof bodies. "
           "The catalogue body links a Lean documentation page lean/docs/317.md at the pin; it is navigation outside the preprints tree, may be fetched only by pinned raw URL and authenticated, and is not source proof reading. "
           "No child catalogue scan, heading locator, read_text/readlines/whole read_bytes/decode or extra family. Full-tree metadata predicates use casefolded FULL paths. Selector failure is disclosed, never authorization for a wider span.")

assert new[41].startswith("Read these exact COMPLETED originals")
new[41] = (
    "Read these exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/: discovery-structural-r192-parent/assessment.md; fresh-structural-discovery-r192/FINAL.md; fresh-structural-discovery-r192/INTERFACES.md; fresh-structural-discovery-r192/DERIVATIONS.md; fresh-structural-discovery-r192/COMPARISON.md; fresh-structural-discovery-r192/private/READING-LIMITS.md. These completed inputs admit no containing namespace or status/activity access; Structural191, Structural190, Structural189 and Structural187 (L²-invariant, finite p-group and K(n)-local/chromatic families) are unrelated to this family and admit no exceptions. "
    "Structural192 remains PREFREEZE/no nominee: on Source316 (Curtis's conjecture) it pays an explicit Laurent basis and contraction for the exterior Milnor-primitive action on the Dickson suspension ideals, the floor-cycle model and its inclusion-compatible filling, a divided-power change of coordinates for all later Milnor primitives, the parity vanishing of all even differentials in the change-of-rings spectral sequence, the exact identification of the degree-two edge kernel as the cokernel of d_3, and a nonzero rank-one d_3 with a nine-term bar filling and an all-odd-exponent residual formula; the all-rank, all-floor, all-even-degree quotient Steenrod action and d_3 compatible with the ideal inclusions remains unpaid, and its stable-homotopy scope is not this family. "
    "Arithmetic159 (uniform weighted-area estimate for the marked Dloussky–Teleman reference curves of minimal class-VII families at every supercritical exponent unpaid), Structural191 (full-scope finite-support filling columns with simultaneous power-decay residual and power-growth norm bounds for finite aspherical integral PD4 complexes unpaid), Arithmetic158 (vanishing of the once-squared determinant class in T(A_f)/(T(Q)det K) with saturated 2-torsion and conductor residues at 3,5,7,11,13 unpaid), Structural190 (structural finite-precision elimination or global chain exchange with an a priori stabilization bound for cyclic lengths of finite p-group products unpaid), Structural189 (source-specific effectively represented all-orders chain contraction in the deformation-adic filtration unpaid), Structural188 (collapse-preserving lift c_S θ̃=θ c_j for every freely adjoined coherator operation after globular-sum gluing unpaid), Structural187 (effective sampling constants/coordinate transfer or all-strata orbit-ideal lifting unpaid), Arithmetic157 (good-point/moving-center multiple-scale normalization anchor for finite-volume semialgebraic domains unpaid), Arithmetic155 (geometric control of the low places spendable by negative small diagrams in generalized-canonical Kähler fourfold flip sequences unpaid), Arithmetic154 (continuation of the quintic stability family through s=0 to the Gepner point unpaid), Arithmetic153 (geometric integrally marked gluing transport unpaid), Arithmetic152 (exact marked cancellation at the original exponent for b≥302 unpaid), Arithmetic151 (global holomorphic correction outside Calabi–Yau-base cases unpaid), Arithmetic150, Structural186 (uniform mixed overlap/attachment control across distinct extensions unpaid), Structural185, Arithmetic149/148, Structural184 and Analytic177 remain PREFREEZE/no nominee at their exact gaps. No retry/general impossibility. "
    "Arithmetic156 (Source057 root-stack fundamental-group isomorphism for the four-factor diagonal-quadric eightfold), Arithmetic147, S183N, S182P, Analytic161/T337A161 and T366A166 are whole-scope PASS/TECHNICAL, correctness conditions DISCHARGED, ZERO count; no bodies admitted or desired-grade retries. S176A remains correctness INCOMPLETE and contribution TECHNICAL conditional on full correctness, condition UNDISCHARGED; no necessary repair/counterexample established. T054L136 remains UNRESOLVED_FULL_SCOPE_REPAIR and NEEDS_REPAIR/INCOMPLETE. "
    "All older full targets/dispositions remain immutable, including every Thomason model structure, Street nerve and orientals, strict and weak higher categories, globular and ω-categories, Grothendieck test categories and Ara–Maltsiniotis homotopy theory, Quillen model structures and Quillen equivalences, Kan Ex and subdivision Sd functors, simplicial sets and homotopy types, coherator and globular-sum scope (including Structural188's) encountered in eligible ORIGINAL history."
)

assert new[43].startswith("Your ONE developed family is confirmed SOURCE316")
new[43] = ("Your ONE developed family is confirmed SOURCE317: THOMASON MODEL STRUCTURES IN ALL STRICT HIGHER DIMENSIONS. ONE canonical manuscript folder, THIRTEEN tree blobs: wrapper build/paper.tex of 3804 bytes, nine section inputs under build/sections numbered 01-introduction, 02-foundations, 03-relative-prisms, 04-labelled-pieces, 05-couniversality, 06-subdivided-attachments, 07-model-structure, 08-method-context and 09-presentability, build/references.bib, README and compiled PDF (two further tree entries are the build and build/sections directories). "
           "Parent infers nothing from filenames; establish from the wrapper which inputs are actually included and in what order, and from the bodies what each section states and proves. Authenticate ALL thirteen blobs; read actual FULL statements and ALL operative includes/required companions, strongest actual primary versions and relevant operative ORIGINAL history mechanisms BEFORE extended deductions or author drafting; disclose exactly which sections were not semantically read. "
           "Source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Validate new deductions/applicability, never audit source truth because it resolves a previously open conjecture.")

assert new[46].startswith("preprints/The-Stable-Hurewicz")
new[46] = PRE + "build/paper.tex"
assert new[47].startswith("bytes762")
new[47] = "bytes3804; Git blob%s." % WRAP_SHA

assert new[49].startswith("Follow actual nested includes")
new[49] = (
    "Follow actual nested includes/ancestors and complete-tree same-family objects, including every section input and the bibliography actually included by the wrapper; no guessed wrapper and no inference of a section's content from its filename. "
    "The source already proves, per catalogue: the Ara–Maltsiniotis conjecture, that for every 1≤n≤∞ (every n≥1 and n=ω) the category of small strict globular n-categories admits a proper combinatorial model structure Quillen equivalent to simplicial sets, with weak equivalences and fibrations detected by the twice-extended Street nerve Ex²N_n and the Quillen equivalence given by c_n Sd² ⊣ Ex²N_n; thus strict higher categories model the homotopy theory of spaces in every positive finite dimension and in dimension ω. "
    "These headlines, the foundations, relative-prism, labelled-piece, couniversality, subdivided-attachment, model-structure and presentability constructions as the bodies actually perform them, the classical Thomason, Street, Kan Ex/Sd, Ara–Maltsiniotis, Gagna, Cisinski and Grothendieck test-category inputs as the bodies actually use them, and any compiled case analyses are paid, not nominees. "
    "Read the actual mechanism (how the generating cofibrations and trivial cofibrations are built, how the Street nerve and its double Ex extension detect weak equivalences and fibrations, where properness, combinatoriality and presentability are each established, how the left adjoint c_n Sd² is controlled on subdivided attachments and relative prisms, how the finite-dimensional cases and the ω case are each handled, and which classical results are inputs versus outputs), the exact definitions and conventions in this manuscript, and any limitation, non-uniqueness or open-case statements the source itself contains. "
    "Do NOT infer statements for weak or non-globular higher categories, for other nerves or other numbers of Ex extensions, for cubical, simplicial or other shape categories beyond those stated, for monoidal, enriched or (∞,n)-categorical refinements, for homotopy hypothesis statements beyond the stated Quillen equivalences, for Thomason-type structures on other categories, for comparisons with Structural188's coherator scope, or for explicit smallness or cardinality bounds, from the proved statements. Stipulate every source operation rather than rejecting the headline by older partial results."
)

assert new[51].startswith("Develop a DISTINCT")
new[51] = new[51].replace("source Hurewicz-image/weight-filtration/algebraic mechanisms", "source nerve-detection/subdivision/attachment/presentability mechanisms")
new[51] = new[51].replace("routine prime, degree, space or spectrum substitutions, unsupported extension to odd primes, unstable or other-spectrum Hurewicz images, Eccles-type statements for other manifolds, Kervaire-existence or Mahowald-type consequences, unsupported explicit bounds or uniformity claims",
                          "routine dimension, nerve or shape substitutions, unsupported extension to weak, non-globular, enriched or (∞,n)-categorical settings, other Ex counts or other base categories, homotopy-hypothesis or coherator consequences, unsupported explicit bounds or uniformity claims")
assert "nerve-detection/subdivision" in new[51] and "weak, non-globular" in new[51]

text = "\n".join(new)
assert len(new) == 76
for bad in ["r192-brief", "SOURCE316", "538801", "Stable-Hurewicz", "eb745886", "bytes762", "TWELVE", "*structural*r192* before", "fresh-structural-discovery-r191/", "discovery-structural-r191-parent", "Arithmetic159 (Source060, its author root", "proof-route", "Hurewicz-image/weight", "odd primes, unstable", "The body links no Lean"]:
    assert bad not in text, bad
assert text.count("Curtis") == 1 and "Curtis" in new[41] and text.count("Singer") == 0
assert "fresh-structural-discovery-r193/" in text and "[539611,540867)" in text and "*arithmetic*r160*" in text and "*structural*r193*" in text and "lean/docs/317.md" in text
out = os.path.join(ET, "fresh-structural-r193-brief.txt")
assert not os.path.exists(out)
open(out, "w", encoding="utf-8").write(text)
raw = open(out, "rb").read()
BRIEF_SHA, BRIEF_BYTES = sha(raw), len(raw)

json.dump({
    "observed_utc": NOW,
    "before_structural193_root_and_brief_dispatch": True,
    "live_peers_at_composition": "Arithmetic160 (Source062, dispatched by parent thread 6742db91-d35c-44d0-a762-e5d9232f5177 at commit d362a37b73) running, not inspected or steered; sole active peer",
    "mutual_guards": {"this_brief_contains": "*arithmetic*r160* (supplement line, inherited) and the explicit peer-namespace exclusion including *owner-recovery*",
                      "peer_brief_contains": "*structural*r193* (supplement line of the original Arithmetic160 brief, SHA256 fc3e00945f860102ce234e445abad730343a09a9f1210ca479512e1198f84e74) and the inherited explicit exclusion of unopened structural rounds"},
    "closed_round_excluded": {"Arithmetic156": "CLOSED PASS/TECHNICAL zero count; namespace excluded from broad selection; no bodies admitted"},
    "no_live_body_status_activity_or_findings_read": True,
    "completed_inputs_read_by_parent_before_brief": [
        "discovery-structural-r192-parent/assessment.md (parent-authored)",
        "fresh-structural-discovery-r192/FINAL.md, REPORT.md, DERIVATIONS.md, COMPARISON.md, RESEARCH-NOTES.md, ANCHORS.json, verify_packet.py, private/READING-LIMITS.md and private record schemas (at the r192 intake)",
    ],
    "limits": "Initial prompt chronology, not OS/perfect isolation.",
    "new_root_created_after_initial_guards_and_before_dispatch": True,
    "new_brief": {"path": "expanded-target-2026-10-17/fresh-structural-r193-brief.txt", "sha256": BRIEF_SHA, "bytes": BRIEF_BYTES},
    "prospective_guard_supplement_in_brief": "carried: *arithmetic*r160*..r162*, *structural*r195*..r197*, *analytic*r187*..r189*; plus the no-r wildcard-twin instruction and a new explicit pre-traversal policy-comparison instruction naming *k369r134-* and *t185r144-* (closing the r192 parser omission prospectively)",
    "completed_exceptions_granted": "r192 FINAL/INTERFACES/DERIVATIONS/COMPARISON/READING-LIMITS and parent assessment; r191 exceptions withdrawn (unrelated L2-invariant family, listed with its unpaid operation)",
    "source317_preparation": {
        "one_family": True,
        "catalogue_extent": list(EXT),
        "catalogue_sha256": BODY_SHA,
        "next_header_located_by_one_bounded_4000_byte_seek": True,
        "incidental_catalogue_display": "318 title displayed in the bounded window as navigation only",
        "title_only_navigation_range": [300, 319],
        "canonical_objects": 13,
        "canonical_folders": 1,
        "tree_entries": 15,
        "lean_docs_link": "lean/docs/317.md",
        "parent_read_source_proofs": False,
    },
}, open(os.path.join(HERE, "prospective-isolation.json"), "w"), indent=1)

root = os.path.join(C, "fresh-structural-discovery-r193")
os.mkdir(root)
print(json.dumps({"brief_sha256": BRIEF_SHA, "brief_bytes": BRIEF_BYTES, "root": root, "title319": title319, "body_sha256": BODY_SHA, "wrap_sha": WRAP_SHA}))
