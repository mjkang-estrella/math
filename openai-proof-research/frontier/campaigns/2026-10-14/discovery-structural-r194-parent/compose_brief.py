#!/usr/bin/env python3
"""Compose the Structural195 brief from the Structural194 brief and write the
Source319 navigation records for the Structural194 parent intake."""
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


# --- Source319 catalogue body and navigation -------------------------------
EXT = (544391, 545514)
with open(os.path.join(PROJ, "sources/CONTENTS.md"), "rb") as f:
    f.seek(EXT[0])
    body = f.read(EXT[1] - EXT[0])
    f.seek(EXT[1])
    nxt = f.read(4000)
assert body.startswith(b"**319. Counterexamples to finite generation at chromatic height two.**")
assert nxt.startswith(b"**320. Nonhomeomorphic closed aspherical four-manifolds.**")
i321 = nxt.find(b"**321. ")
assert i321 >= 0
assert b"lean/docs" not in body
BODY_SHA = sha(body)
assert BODY_SHA == "96ee44bd172daac534d5655e2d9c88fa010e099d917c59878e0bc78a22705a97"
with open(os.path.join(PRIV, "catalogue-319.md"), "wb") as f:
    f.write(body)

nav_src = os.path.join(C, "discovery-structural-r193-parent/private/title-navigation.json")
nav = json.load(open(nav_src))
assert nav["families_selected"][-1] == {"family": 318, "round": "structural194"}
assert nav["next_header"]["family"] == 319 and nav["next_header"]["start"] == EXT[0]
title321 = nxt[i321:nxt.find(b".**", i321) + 3].decode()
nav["numeric_range"] = [300, 321]
nav["titles"].append({"family": 321, "start": EXT[1] + i321,
                      "title_end": EXT[1] + i321 + len(title321.encode()),
                      "raw": title321})
nav["families_selected"].append({"family": 319, "round": "structural195"})
nav["next_header"] = {"family": 320, "start": EXT[1],
                      "located_by": "320 header located at the structural194 dispatch by one bounded 4000-byte seek after 544391; body [544391,545514) decoded once for structural195 selection; 321 header located by one bounded 4000-byte seek after 545514",
                      "incidental_display": "the bounded window after 545514 displayed the 320 title and its opening words to the parent as navigation only; no source theorem/proof body was read and no family other than 319 was selected"}
json.dump(nav, open(os.path.join(PRIV, "title-navigation.json"), "w"), indent=1)

# --- folder metadata (one manuscript) -------------------------------------------
tree = json.load(open(os.path.join(PROJ, "sources/preprints-tree.json")))["tree"]
assert len(tree) == 13223
FO = "Counterexamples-to-the-Hahn-Wilson-conjecture-at-height-two-September-26-2026"
PRE = "preprints/" + FO + "/"
bodytxt = body.decode()
assert bodytxt.count("](preprints/") == 1 and "](" + PRE + "paper.pdf)" in bodytxt
fam = [e for e in tree if e["path"].startswith(PRE)]
blobs = [e for e in fam if e["type"] == "blob"]
assert (len(fam), len(blobs)) == (14, 12), (len(fam), len(blobs))
w = [e for e in blobs if e["path"] == PRE + "build/main.tex"][0]
assert w["size"] == 14864 and w["sha"] == "1232983b9757fad0d6fc659478cd6198e52021a5", w
names = sorted(e["path"][len(PRE):] for e in blobs)
assert names == ["README.md", "build/main.tex", "build/references.tex", "build/sections/comparison.tex", "build/sections/completion.tex", "build/sections/consequences.tex", "build/sections/geometry.tex", "build/sections/gluing.tex", "build/sections/obstruction.tex", "build/sections/operator.tex", "build/sections/transfer.tex", "paper.pdf"], names
assert sum(1 for n in names if n.endswith(".tex") and not n.endswith("main.tex") and not n.endswith("references.tex")) == 8
others = [e["path"] for e in tree if any(k in e["path"].lower() for k in ("hahn-wilson", "hahn_wilson", "fp-type")) and not e["path"].startswith(PRE.rstrip("/"))]
assert not others, others
# a distinct family folder (not linked from the Source319 body) shares the finite-generation keyword; it is not selected
neighbor = sorted({e["path"].split("/")[1] for e in tree if "finite-generation" in e["path"].lower() and not e["path"].startswith(PRE.rstrip("/"))})
assert neighbor == ["Finite-generation-for-the-Kn-local-sphere-September-24-2026"], neighbor
sel = {"family": 319, "catalogue_extent": list(EXT), "catalogue_sha256": BODY_SHA,
       "next_header_confirmed": "**320. Nonhomeomorphic closed aspherical four-manifolds.** at 545514 (located earlier); 321 header at %d" % (EXT[1] + i321),
       "folders": [PRE.rstrip("/")], "blobs_per_folder": [12], "tree_entries_per_folder": [14],
       "candidate_top_level_tex": ["build/main.tex (14864 B, blob %s)" % w["sha"]], "blob_names_only": {FO: names},
       "bibliography_form": "build/references.tex (no .bib in the folder; parent infers nothing about how it is included)",
       "lean_docs_link": False, "parent_read_source_proofs": False, "total_blobs": 12,
       "history_note": "frontier/iterations/i105-chromatic-homotopy-discovery.md names the Hahn-Wilson paper as a title/search comparison only, not a theorem dependency (parent grep of the authored iteration, line 24)",
       "unselected_keyword_neighbor": "preprints/Finite-generation-for-the-Kn-local-sphere-September-24-2026 (distinct catalogue family, not linked from the Source319 body; metadata only, not selected)"}
json.dump(sel, open(os.path.join(PRIV, "source319-selection.json"), "w"), indent=1)
WRAP = (PRE + "build/main.tex", 14864, w["sha"])

# --- brief --------------------------------------------------------------------
ET = os.path.join(C, "expanded-target-2026-10-17")
old = open(os.path.join(ET, "fresh-structural-r194-brief.txt"), encoding="utf-8").read().split("\n")
assert len(old) == 84
new = list(old)
assert new[0].startswith("Structural discovery r194")
new[0] = "Structural discovery r195 — confirmed Hahn–Wilson counterexample at chromatic height two (connective p-complete exact fp-type-two spectrum outside the BP⟨2⟩ thick subcategory with both localization comparisons, sufficiently large p) operative-proof discovery."
new[1] = "Write ONLY frontier/campaigns/2026-10-14/fresh-structural-discovery-r195/."

a = new[9].index("The ORIGINAL INITIAL brief of Arithmetic162")
b = new[9].index("Exact COMPLETED exceptions do not widen containing directories.") + len("Exact COMPLETED exceptions do not widen containing directories.")
new[9] = new[9][:a] + (
    "The ORIGINAL INITIAL brief of Arithmetic162c, dispatched before this round, contains the literal prospective guard *structural*r195* before any structural195 body existed, and this brief contains *arithmetic*r162* while arithmetic162c is live. "
    "Arithmetic162c (Source066, author root fresh-arithmetic-discovery-r162c and its parent records, all inside the arithmetic162 namespace together with the archived Arithmetic162 and Arithmetic162b rounds and the progress-2026-10-22-owner-recovery parent directory) is the only current active peer: exclude the ENTIRE *arithmetic*r162* namespace, *owner-recovery* and every body/parent/brief/copy/derivative/status/activity alias. "
    "Arithmetic156 is COMPLETED and CLOSED whole-scope PASS/TECHNICAL with ZERO count (its author root, both review roots and parent records are no longer live): exclude the ENTIRE *arithmetic*r156* namespace from broad selection; no bodies admitted. "
    "Structural194, Arithmetic162b, Arithmetic162, Structural193, Arithmetic161, Arithmetic160, Structural192, Arithmetic159, Structural191, Arithmetic158, Structural190, Structural189, Arithmetic157, Arithmetic155, Structural188, Structural187, Arithmetic154, Arithmetic153, Structural186, Arithmetic152, Arithmetic151 and Arithmetic150 are COMPLETED PREFREEZE/no nominee and parent-archived; exclude every structural194, arithmetic162, structural193, arithmetic161, arithmetic160, structural192, arithmetic159, structural191, arithmetic158, structural190, structural189, arithmetic157, arithmetic155, structural188, structural187, arithmetic154, arithmetic153, structural186, arithmetic152, arithmetic151 and arithmetic150 namespace from broad selection; only the exact COMPLETED exceptions below are direct reads. "
    "Also exclude every full-path alias of a completed or live round that lacks the literal r (for example arithmetic151-stopped.json style status aliases, arithmetic15N*, arithmetic16N*, structural19N*, analytic18N*) by installing the no-r wildcard twins of every listed guard before traversal, and verify by an explicit policy comparison BEFORE traversal that every literal guard listed in this brief, including *k369r134-* and *t185r144-*, and its no-r twin is actually installed. "
    "Own structural195 namespace remains excluded from broad authored-history scans; own files usable. No peer body/status/activity/summary/finding may be inspected, inferred or used as premise. Do not inspect or steer peers to certify supplied isolation. This is prompt chronology, not OS/perfect isolation. Exact COMPLETED exceptions do not widen containing directories."
) + new[9][b:]

assert new[37].startswith("Additionally install prospective FULL-PATH wildcard guards *arithmetic*r160*") and new[38] == ""
new[37] = ("Additionally install prospective FULL-PATH wildcard guards *arithmetic*r160*,*arithmetic*r161*,*arithmetic*r162*,*arithmetic*r163*,*arithmetic*r164*,*arithmetic*r165*,*arithmetic*r166*,*arithmetic*r167*,*arithmetic*r168*,*structural*r195*,*structural*r196*,*structural*r197*,*structural*r198*,*structural*r199*,*structural*r200*,*structural*r201*,*structural*r202*,*structural*r203*,*analytic*r187*,*analytic*r188*,*analytic*r189*,*analytic*r190*,*analytic*r191*,*analytic*r192*,*analytic*r193*,*analytic*r194*,*analytic*r195* BEFORE traversal/body selection, supplementing EVERY earlier literal guard.")

assert new[39].startswith("Catalogue access for THIS round")
new[39] = ("Catalogue access for THIS round, if needed at all: ONLY direct binary seek/read sources/CONTENTS.md[544391,545514), confirmed exact Source319 body. "
           "Parent reused numeric-header TITLE-ONLY300–320, located the 321 header by one bounded 4000-byte seek after 545514 (that window displayed the 320 title and its opening words to the parent as navigation only) and selected ONLY this family; parent has NOT read source theorem/proof bodies. The body links no Lean documentation page. "
           "No child catalogue scan, heading locator, read_text/readlines/whole read_bytes/decode or extra family. Full-tree metadata predicates use casefolded FULL paths. Selector failure is disclosed, never authorization for a wider span.")

assert new[41].startswith("Read these exact COMPLETED originals")
new[41] = (
    "Read these exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/: discovery-structural-r194-parent/assessment.md; fresh-structural-discovery-r194/FINAL.md; fresh-structural-discovery-r194/INTERFACES.md; fresh-structural-discovery-r194/DERIVATIONS.md; fresh-structural-discovery-r194/COMPARISON.md; fresh-structural-discovery-r194/private/READING-LIMITS.md. These completed inputs admit no containing namespace or status/activity access; Structural193, Structural192, Structural191, Structural190, Structural189 and Structural187 (Thomason model structures, stable Hurewicz, L²-invariant, finite p-group, deformation-adic and K(n)-local invariant-ideal families) are unrelated to this family's thick-subcategory/fp-type mechanism and admit no exceptions. "
    "Structural194 remains PREFREEZE/no nominee: on Source318 (chromatic splitting filtrations and counterexamples, five manuscripts) it pays, at p≥5, a determinant-compatible C-linear module reduction X=L_2L_{K(3)}S_p^∧≃C⊗_{L_2S}(P∨Q[−5]∨Q[−8]) with C the localized circle cochains and A_2→P→A_1[−3]→ΣA_2 the nonzero middle attachment, a fully faithful left adjoint Mod_C→Fun(BZ,Mod_{A_2}) with an explicit counit cone N on which ψ−1 is invertible, and at p=3 the generic detector sections by the unit and the mod-three-normalized determinant class isolating a δ-character exterior pair in degrees −3,−4; vanishing of that residual cone with the original continuous action and an integral spectral realization of the δ generator compatible with all cooperations remain unpaid, and its chromatic-splitting scope is adjacent to but not this family's finite-generation question. "
    "Arithmetic162b (full mixed relative Virasoro intertwiner with vanishing cap-image residual, all modes/cutoffs, scalar normalization and integral-class gluing unpaid), Arithmetic162 (full ambient joint bi-Hölder completion across nonzero Milnor levels with bilateral two-point bounds unpaid), Structural193 (positive strict realization of the signed Street-nerve chain contraction as stationary RIGHT Gray-cylinder zigzags in every dimension with coherent finite-piece realization unpaid), Arithmetic161 (eliminating the divisor-supported all-minimal quantum word for full defect-two low-degree chain connectivity unpaid), Arithmetic160 (full global contact tensor with correct all-sheet jets and boundary compatibility unpaid), Structural192 (all-rank, all-floor, all-even-degree quotient Steenrod action and compatible d_3 on the Dickson suspension ideals unpaid), Arithmetic159 (uniform weighted-area estimate for the marked Dloussky–Teleman reference curves of minimal class-VII families at every supercritical exponent unpaid), Structural191 (full-scope finite-support filling columns with simultaneous power-decay residual and power-growth norm bounds for finite aspherical integral PD4 complexes unpaid), Arithmetic158 (vanishing of the once-squared determinant class in T(A_f)/(T(Q)det K) with saturated 2-torsion and conductor residues at 3,5,7,11,13 unpaid), Structural190 (structural finite-precision elimination or global chain exchange with an a priori stabilization bound for cyclic lengths of finite p-group products unpaid), Structural189 (source-specific effectively represented all-orders chain contraction in the deformation-adic filtration unpaid), Structural188 (collapse-preserving lift c_S θ̃=θ c_j for every freely adjoined coherator operation after globular-sum gluing unpaid), Structural187 (effective sampling constants/coordinate transfer or all-strata orbit-ideal lifting unpaid), Arithmetic157 (good-point/moving-center multiple-scale normalization anchor for finite-volume semialgebraic domains unpaid), Arithmetic155 (geometric control of the low places spendable by negative small diagrams in generalized-canonical Kähler fourfold flip sequences unpaid), Arithmetic154 (continuation of the quintic stability family through s=0 to the Gepner point unpaid), Arithmetic153 (geometric integrally marked gluing transport unpaid), Arithmetic152 (exact marked cancellation at the original exponent for b≥302 unpaid), Arithmetic151 (global holomorphic correction outside Calabi–Yau-base cases unpaid), Arithmetic150, Structural186 (uniform mixed overlap/attachment control across distinct extensions unpaid), Structural185, Arithmetic149/148, Structural184 and Analytic177 remain PREFREEZE/no nominee at their exact gaps. No retry/general impossibility. "
    "Arithmetic156 (Source057 root-stack fundamental-group isomorphism for the four-factor diagonal-quadric eightfold), Arithmetic147, S183N, S182P, Analytic161/T337A161 and T366A166 are whole-scope PASS/TECHNICAL, correctness conditions DISCHARGED, ZERO count; no bodies admitted or desired-grade retries. S176A remains correctness INCOMPLETE and contribution TECHNICAL conditional on full correctness, condition UNDISCHARGED; no necessary repair/counterexample established. T054L136 remains UNRESOLVED_FULL_SCOPE_REPAIR and NEEDS_REPAIR/INCOMPLETE. "
    "All older full targets/dispositions remain immutable, including the Hahn–Wilson conjecture at every height, fp-type and BP⟨n⟩ thick-subcategory and finite-generation scope, finite and telescopic localization comparisons L_n^f/L_n and L_{T(n)}/L_{K(n)}, telescope conjecture and thick-subcategory scope (including Structural187's and Structural189's), chromatic splitting and fracture scope (including Structural194's), K(n)- and E(n)-localization, Morava E-theory and stabilizer group, derived p-completion, Adams–Novikov and β-family encountered in eligible ORIGINAL history; the completed iteration i105 names the Hahn–Wilson paper only as a title/search comparison, not as a dependency."
)

assert new[43].startswith("Your ONE developed family is confirmed SOURCE318")
new[43] = ("Your ONE developed family is confirmed SOURCE319: COUNTEREXAMPLES TO FINITE GENERATION AT CHROMATIC HEIGHT TWO. ONE canonical manuscript folder, TWELVE tree blobs: "
           "Counterexamples-to-the-Hahn-Wilson-conjecture-at-height-two (September-26; wrapper build/main.tex of 14864 bytes, build/references.tex, eight named section inputs under build/sections — comparison, completion, consequences, geometry, gluing, obstruction, operator, transfer — README, compiled PDF; twelve blobs, fourteen tree entries). "
           "Parent infers nothing from filenames or the absence of numbering; establish from the wrapper which inputs are actually included and in what order, how references.tex enters, and from the bodies what the manuscript states and proves. Authenticate ALL twelve blobs; read actual FULL statements and ALL operative includes/required companions, strongest actual primary versions and relevant operative ORIGINAL history mechanisms BEFORE extended deductions or author drafting; disclose exactly which sections were not semantically read. "
           "Source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Validate new deductions/applicability, never audit source truth because it refutes a previously open conjecture.")

assert new[45] == "Confirmed canonical wrappers at immutable pin:" and new[46].startswith("preprints/Filtered") and new[55].startswith("bytes1122") and new[56] == ""
new[45:56] = ["Confirmed canonical wrapper at immutable pin:", WRAP[0], "bytes%d; Git blob%s." % (WRAP[1], WRAP[2])]  # 84 -> 76 lines
assert len(new) == 76
K = -8  # index shift for everything after the wrapper block

assert new[57 + K].startswith("Follow actual nested includes")
new[57 + K] = (
    "Follow actual nested includes/ancestors and complete-tree same-family objects, including every section input and the references file actually included by the wrapper; no guessed wrapper and no inference of a section's content from its filename. "
    "The source already proves, per catalogue: for every sufficiently large prime p there is a connective p-complete spectrum X of exact fp-type two outside the ordinary thick subcategory generated by the specified standard form of BP⟨2⟩_p^∧ (finitely many sums, shifts, cones and retracts), and the same X satisfies both localization comparisons L_2^fX≃L_2X and L_{T(2)}X≃L_{K(2)}X; this refutes the Hahn–Wilson conjecture at height two. "
    "This headline, the obstruction, operator, transfer, gluing, geometry, completion, comparison and consequence constructions as the body actually performs them, the Hahn–Wilson formulation, Mahowald–Rezk fp-type, BP⟨n⟩ and its standard forms, Morava K- and E-theory, telescope/finite-localization and Adams–Novikov inputs as the body actually uses them, and any compiled case analyses are paid, not nominees. "
    "Read the actual mechanism (what sufficiently large prime means and where the bound is used, how exact fp-type two is defined and verified for X, what the specified standard form of BP⟨2⟩ is and whether other forms are addressed, how the thick-subcategory obstruction is detected and why it survives sums, shifts, cones and retracts, how each localization comparison is proved, which statements are about underlying spectra versus modules or structured objects, and which classical results are inputs versus outputs), the exact definitions and conventions, and any limitation, non-uniqueness or open-case statements the source itself contains. "
    "Do NOT infer statements for small primes, for other heights or the full Hahn–Wilson conjecture elsewhere, for other forms of BP⟨2⟩ or other thick subcategories, for explicit prime bounds, for telescope-type statements beyond the two proved comparisons, for Picard, duality or K-theoretic consequences, or for finite-generation statements about other spectra, from the proved statement. Stipulate every source operation rather than rejecting the headline by older partial results."
)

assert new[59 + K].startswith("Develop a DISTINCT")
new[59 + K] = new[59 + K].replace("source fracture/filtration/tower/descent-exponent mechanisms", "source obstruction/operator/transfer/gluing/comparison mechanisms")
new[59 + K] = new[59 + K].replace("routine prime, height or spectrum substitutions, unsupported extension to small primes, other heights or other localized spheres and finite complexes, finite-assembly or splitting statements in ranges the sources do not treat, telescope-type, Picard or duality consequences, unsupported explicit bounds or uniformity claims",
                                  "routine prime, height or spectrum substitutions, unsupported extension to small primes, other heights or other BP⟨n⟩ forms, thick-subcategory or localization-comparison statements in ranges the source does not treat, telescope-type, Picard or duality consequences, unsupported explicit prime bounds or uniformity claims")
assert "obstruction/operator/transfer" in new[59 + K] and "other BP⟨n⟩ forms" in new[59 + K]

text = "\n".join(new)
for bad in ["r194-brief", "SOURCE318", "540867", "Filtered-chromatic", "66a0d3da", "bytes918", "EIGHTY-FIVE", "*structural*r194* before", "fresh-structural-discovery-r193/", "discovery-structural-r193-parent", "fracture/filtration/tower", "Confirmed canonical wrappers at", "Arithmetic162 (Source064, its author root"]:
    assert bad not in text, bad
assert text.count("Thomason") == 1 and "Thomason" in new[41] and text.count("Gray") == 1
assert "fresh-structural-discovery-r195/" in text and "[544391,545514)" in text and "*arithmetic*r162*" in text and "*structural*r195*" in text and "*arithmetic*r166*" in text
assert sum(1 for l in new if l.startswith("preprints/")) == 1 and sum(1 for l in new if l.startswith("bytes")) == 1
out = os.path.join(ET, "fresh-structural-r195-brief.txt")
assert not os.path.exists(out)
open(out, "w", encoding="utf-8").write(text)
raw = open(out, "rb").read()
BRIEF_SHA, BRIEF_BYTES = sha(raw), len(raw)

json.dump({
    "observed_utc": NOW,
    "before_structural195_root_and_brief_dispatch": True,
    "live_peers_at_composition": "Arithmetic162c (Source066, idx654, dispatched by parent thread 6742db91-d35c-44d0-a762-e5d9232f5177 at commit e2a071e5d3) running, not inspected or steered; sole active peer at composition (ledger re-read immediately before composing); its root fresh-arithmetic-discovery-r162c and records lie inside the *arithmetic*r162* namespace",
    "mutual_guards": {"this_brief_contains": "*arithmetic*r162* (supplement line) and the explicit peer-namespace exclusion including *owner-recovery*; prospective *arithmetic*r166*..r168*, *structural*r201*..r203*, *analytic*r193*..r195* added",
                      "peer_brief_contains": "*structural*r195* (original Arithmetic162c brief, SHA256 1cdbef578466878ace43b6a1912a1119085fd21fcf0996d30a1e9c7a60b657f1; parent grep count 1)"},
    "closed_round_excluded": {"Arithmetic156": "CLOSED PASS/TECHNICAL zero count; namespace excluded from broad selection; no bodies admitted"},
    "no_live_body_status_activity_or_findings_read": True,
    "completed_inputs_read_by_parent_before_brief": [
        "discovery-structural-r194-parent/assessment.md (parent-authored)",
        "fresh-structural-discovery-r194/FINAL.md, REPORT.md, DERIVATIONS.md, COMPARISON.md, ANCHORS.json, verify_packet.py, private/READING-LIMITS.md and private record schemas (at the r194 intake)",
    ],
    "limits": "Initial prompt chronology, not OS/perfect isolation.",
    "new_root_created_after_initial_guards_and_before_dispatch": True,
    "new_brief": {"path": "expanded-target-2026-10-17/fresh-structural-r195-brief.txt", "sha256": BRIEF_SHA, "bytes": BRIEF_BYTES, "lines": 76},
    "prospective_guard_supplement_in_brief": "extended: *arithmetic*r160*..r168*, *structural*r195*..r203*, *analytic*r187*..r195*; plus the no-r wildcard-twin instruction and the pre-traversal policy-comparison instruction naming *k369r134-* and *t185r144-*",
    "completed_exceptions_granted": "r194 FINAL/INTERFACES/DERIVATIONS/COMPARISON/READING-LIMITS and parent assessment; r193 exceptions withdrawn (unrelated Thomason family, listed with its unpaid operation)",
    "source319_preparation": {
        "one_family": True,
        "catalogue_extent": list(EXT),
        "catalogue_sha256": BODY_SHA,
        "next_header_located_by_one_bounded_4000_byte_seek": True,
        "incidental_catalogue_display": "320 title and opening words displayed in the bounded window as navigation only",
        "title_only_navigation_range": [300, 321],
        "canonical_objects": 12,
        "canonical_folders": 1,
        "tree_entries": 14,
        "wrappers": [{"path": WRAP[0], "bytes": WRAP[1], "git_blob": WRAP[2]}],
        "lean_docs_link": False,
        "parent_read_source_proofs": False,
    },
}, open(os.path.join(HERE, "prospective-isolation.json"), "w"), indent=1)

root = os.path.join(C, "fresh-structural-discovery-r195")
os.mkdir(root)
print(json.dumps({"brief_sha256": BRIEF_SHA, "brief_bytes": BRIEF_BYTES, "lines": len(new), "root": root, "title321": title321, "body_sha256": BODY_SHA}))
