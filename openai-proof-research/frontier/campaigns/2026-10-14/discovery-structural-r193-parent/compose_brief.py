#!/usr/bin/env python3
"""Compose the Structural194 brief from the Structural193 brief and write the
Source318 navigation records for the Structural193 parent intake."""
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


# --- Source318 catalogue body and navigation -------------------------------
EXT = (540867, 544391)
with open(os.path.join(PROJ, "sources/CONTENTS.md"), "rb") as f:
    f.seek(EXT[0])
    body = f.read(EXT[1] - EXT[0])
    f.seek(EXT[1])
    nxt = f.read(4000)
assert body.startswith(b"**318. Chromatic splitting: filtrations and counterexamples.**")
assert nxt.startswith(b"**319. Counterexamples to finite generation at chromatic height two.**")
i320 = nxt.find(b"**320. ")
assert i320 >= 0
assert b"lean/docs" not in body
BODY_SHA = sha(body)
assert BODY_SHA == "e84108b781fe07f20fe9d4d6d10cd0cda593ecbb7588ae0df2d0cc83887eaa76"
with open(os.path.join(PRIV, "catalogue-318.md"), "wb") as f:
    f.write(body)

nav_src = os.path.join(C, "discovery-structural-r192-parent/private/title-navigation.json")
nav = json.load(open(nav_src))
assert nav["families_selected"][-1] == {"family": 317, "round": "structural193"}
assert nav["next_header"]["family"] == 318 and nav["next_header"]["start"] == EXT[0]
title320 = nxt[i320:nxt.find(b".**", i320) + 3].decode()
nav["numeric_range"] = [300, 320]
nav["titles"].append({"family": 320, "start": EXT[1] + i320,
                      "title_end": EXT[1] + i320 + len(title320.encode()),
                      "raw": title320})
nav["families_selected"].append({"family": 318, "round": "structural194"})
nav["next_header"] = {"family": 319, "start": EXT[1],
                      "located_by": "319 header located at the structural193 dispatch by one bounded 4000-byte seek after 540867; body [540867,544391) decoded once for structural194 selection; 320 header located by one bounded 4000-byte seek after 544391",
                      "incidental_display": "the bounded window after 544391 displayed the 319 title and its opening words to the parent as navigation only; no source theorem/proof body was read and no family other than 318 was selected"}
json.dump(nav, open(os.path.join(PRIV, "title-navigation.json"), "w"), indent=1)

# --- folder metadata (five manuscripts, catalogue order) -----------------------
tree = json.load(open(os.path.join(PROJ, "sources/preprints-tree.json")))["tree"]
assert len(tree) == 13223
FOLDERS = [
    ("Filtered-chromatic-splitting-at-generic-primes-September-25-2026", "build/paper.tex", 918, "66a0d3da071a9cb576c52fa055fa588ab25f5db0", 17, 19),
    ("The-height-three-chromatic-overlap-an-explicit-filtration-and-its-attachments-September-27-2026", "build/paper.tex", 1196, "5dd072e006a3d90800a23ffed661ec6aa1b9fcfa", 18, 20),
    ("A-rational-obstruction-to-strong-chromatic-splitting-at-height-three-September-25-2026", "build/main.tex", 1057, "65324c62fb728f11dd65b8fdd74b0627a52d8d3c", 18, 20),
    ("Failure-of-finite-assembly-for-a-chromatic-overlap-at-the-prime-three-September-25-2026", "build/paper.tex", 3051, "795f08a402bc0d06f4ed1ef24a78b1afa09c3153", 15, 17),
    ("Counterexamples-to-weak-chromatic-splitting-sphere-kernels-and-descent-exponents-September-27-2026", "build/main.tex", 1122, "3ac56b00cf250ad0c47482d2e98426feabdc554b", 17, 19),
]
bodytxt = body.decode()
assert bodytxt.count("](preprints/") == 5
links = [bodytxt[bodytxt.index("](preprints/" + fo) + 2:] for fo, *_ in FOLDERS]
assert all(l.startswith("preprints/" + fo + "/paper.pdf)") for l, (fo, *_) in zip(links, FOLDERS))
order = [bodytxt.index("](preprints/" + fo) for fo, *_ in FOLDERS]
assert order == sorted(order)  # FOLDERS is in catalogue order
sel = {"family": 318, "catalogue_extent": list(EXT), "catalogue_sha256": BODY_SHA,
       "next_header_confirmed": "**319. Counterexamples to finite generation at chromatic height two.** at 544391 (located earlier); 320 header at %d" % (EXT[1] + i320),
       "folders": [], "blobs_per_folder": [], "tree_entries_per_folder": [], "candidate_top_level_tex": [], "blob_names_only": {}, "lean_docs_link": False, "parent_read_source_proofs": False}
WRAPS = []
for fo, wrap, wsize, wsha, nb, ne in FOLDERS:
    PRE = "preprints/" + fo + "/"
    fam = [e for e in tree if e["path"].startswith(PRE)]
    blobs = [e for e in fam if e["type"] == "blob"]
    assert (len(fam), len(blobs)) == (ne, nb), (fo, len(fam), len(blobs))
    w = [e for e in blobs if e["path"] == PRE + wrap][0]
    assert w["size"] == wsize and w["sha"] == wsha, (fo, w)
    names = sorted(e["path"][len(PRE):] for e in blobs)
    assert "paper.pdf" in names and "README.md" in names and "build/references.bib" in names
    sel["folders"].append(PRE.rstrip("/")); sel["blobs_per_folder"].append(nb); sel["tree_entries_per_folder"].append(ne)
    sel["candidate_top_level_tex"].append("%s (%d B, blob %s)" % (wrap, wsize, wsha)); sel["blob_names_only"][fo] = names
    WRAPS.append((PRE + wrap, wsize, wsha))
sel["total_blobs"] = sum(sel["blobs_per_folder"]); assert sel["total_blobs"] == 85 and sum(sel["tree_entries_per_folder"]) == 95
others = [e["path"] for e in tree if any(k in e["path"].lower() for k in ("chromatic-splitting", "chromatic-overlap", "weak-chromatic", "finite-assembly")) and not any(e["path"].startswith(f) for f in sel["folders"])]
assert not others, others
json.dump(sel, open(os.path.join(PRIV, "source318-selection.json"), "w"), indent=1)

# --- brief --------------------------------------------------------------------
ET = os.path.join(C, "expanded-target-2026-10-17")
old = open(os.path.join(ET, "fresh-structural-r193-brief.txt"), encoding="utf-8").read().split("\n")
assert len(old) == 76
new = list(old)
assert new[0].startswith("Structural discovery r193")
new[0] = "Structural discovery r194 — confirmed chromatic splitting filtrations and counterexamples (heights three, p and p+1; generic-prime 2^n-stage filtration; prime-three finite-assembly failure) operative-proof discovery."
new[1] = "Write ONLY frontier/campaigns/2026-10-14/fresh-structural-discovery-r194/."

a = new[9].index("The ORIGINAL INITIAL brief of Arithmetic160")
b = new[9].index("Exact COMPLETED exceptions do not widen containing directories.") + len("Exact COMPLETED exceptions do not widen containing directories.")
new[9] = new[9][:a] + (
    "The ORIGINAL INITIAL brief of Arithmetic162, dispatched before this round, contains the literal prospective guard *structural*r194* before any structural194 body existed, and this brief contains *arithmetic*r162* while arithmetic162 is live. "
    "Arithmetic162 (Source064, its author root and parent records, including the progress-2026-10-22-owner-recovery parent directory) is the only current active peer: exclude the ENTIRE *arithmetic*r162* namespace, *owner-recovery* and every body/parent/brief/copy/derivative/status/activity alias. "
    "Arithmetic156 is COMPLETED and CLOSED whole-scope PASS/TECHNICAL with ZERO count (its author root, both review roots and parent records are no longer live): exclude the ENTIRE *arithmetic*r156* namespace from broad selection; no bodies admitted. "
    "Structural193, Arithmetic161, Arithmetic160, Structural192, Arithmetic159, Structural191, Arithmetic158, Structural190, Structural189, Arithmetic157, Arithmetic155, Structural188, Structural187, Arithmetic154, Arithmetic153, Structural186, Arithmetic152, Arithmetic151 and Arithmetic150 are COMPLETED PREFREEZE/no nominee and parent-archived; exclude every structural193, arithmetic161, arithmetic160, structural192, arithmetic159, structural191, arithmetic158, structural190, structural189, arithmetic157, arithmetic155, structural188, structural187, arithmetic154, arithmetic153, structural186, arithmetic152, arithmetic151 and arithmetic150 namespace from broad selection; only the exact COMPLETED exceptions below are direct reads. "
    "Also exclude every full-path alias of a completed or live round that lacks the literal r (for example arithmetic151-stopped.json style status aliases, arithmetic15N*, arithmetic16N*, structural19N*, analytic18N*) by installing the no-r wildcard twins of every listed guard before traversal, and verify by an explicit policy comparison BEFORE traversal that every literal guard listed in this brief, including *k369r134-* and *t185r144-*, and its no-r twin is actually installed. "
    "Own structural194 namespace remains excluded from broad authored-history scans; own files usable. No peer body/status/activity/summary/finding may be inspected, inferred or used as premise. Do not inspect or steer peers to certify supplied isolation. This is prompt chronology, not OS/perfect isolation. Exact COMPLETED exceptions do not widen containing directories."
) + new[9][b:]

assert new[37].startswith("Additionally install prospective FULL-PATH wildcard guards *arithmetic*r160*") and new[38] == ""
new[37] = ("Additionally install prospective FULL-PATH wildcard guards *arithmetic*r160*,*arithmetic*r161*,*arithmetic*r162*,*arithmetic*r163*,*arithmetic*r164*,*arithmetic*r165*,*structural*r195*,*structural*r196*,*structural*r197*,*structural*r198*,*structural*r199*,*structural*r200*,*analytic*r187*,*analytic*r188*,*analytic*r189*,*analytic*r190*,*analytic*r191*,*analytic*r192* BEFORE traversal/body selection, supplementing EVERY earlier literal guard.")

assert new[39].startswith("Catalogue access for THIS round")
new[39] = ("Catalogue access for THIS round, if needed at all: ONLY direct binary seek/read sources/CONTENTS.md[540867,544391), confirmed exact Source318 body. "
           "Parent reused numeric-header TITLE-ONLY300–319, located the 320 header by one bounded 4000-byte seek after 544391 (that window displayed the 319 title and its opening words to the parent as navigation only) and selected ONLY this family; parent has NOT read source theorem/proof bodies. The body links no Lean documentation page. "
           "No child catalogue scan, heading locator, read_text/readlines/whole read_bytes/decode or extra family. Full-tree metadata predicates use casefolded FULL paths. Selector failure is disclosed, never authorization for a wider span.")

assert new[41].startswith("Read these exact COMPLETED originals")
new[41] = (
    "Read these exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/: discovery-structural-r193-parent/assessment.md; fresh-structural-discovery-r193/FINAL.md; fresh-structural-discovery-r193/INTERFACES.md; fresh-structural-discovery-r193/DERIVATIONS.md; fresh-structural-discovery-r193/COMPARISON.md; fresh-structural-discovery-r193/private/READING-LIMITS.md. These completed inputs admit no containing namespace or status/activity access; Structural192, Structural191, Structural190, Structural189 and Structural187 (stable Hurewicz, L²-invariant, finite p-group, deformation-adic and K(n)-local invariant-ideal families) are unrelated to this family's fracture/filtration mechanism and admit no exceptions. "
    "Structural193 remains PREFREEZE/no nominee: on Source317 (Thomason model structures in all strict higher dimensions) it pays a signed relative Street-nerve chain contraction from the source's stationary prisms, an explicit two-piece overlap correction s'=s−i h_A α with d h_C+h_C d=id, induction over arbitrary attachments with a chain-norm recurrence, the canonical lift to the prescribed retraction, square-zero normalization, higher signed fillers, a finite perturbation contraction of the simplicial replacement over ir-stable finite pieces, an n=1 idempotent-pushout computation and a diamond obstruction to a single right cylinder; positive strict realization of that signed data as stationary RIGHT Gray-cylinder zigzags in every dimension with coherent finite-piece realization remains unpaid, and its higher-category scope is not this family. "
    "Arithmetic161 (eliminating the divisor-supported all-minimal quantum word for full defect-two low-degree chain connectivity unpaid), Arithmetic160 (full global contact tensor with correct all-sheet jets and boundary compatibility unpaid), Structural192 (all-rank, all-floor, all-even-degree quotient Steenrod action and compatible d_3 on the Dickson suspension ideals unpaid), Arithmetic159 (uniform weighted-area estimate for the marked Dloussky–Teleman reference curves of minimal class-VII families at every supercritical exponent unpaid), Structural191 (full-scope finite-support filling columns with simultaneous power-decay residual and power-growth norm bounds for finite aspherical integral PD4 complexes unpaid), Arithmetic158 (vanishing of the once-squared determinant class in T(A_f)/(T(Q)det K) with saturated 2-torsion and conductor residues at 3,5,7,11,13 unpaid), Structural190 (structural finite-precision elimination or global chain exchange with an a priori stabilization bound for cyclic lengths of finite p-group products unpaid), Structural189 (source-specific effectively represented all-orders chain contraction in the deformation-adic filtration unpaid), Structural188 (collapse-preserving lift c_S θ̃=θ c_j for every freely adjoined coherator operation after globular-sum gluing unpaid), Structural187 (effective sampling constants/coordinate transfer or all-strata orbit-ideal lifting unpaid), Arithmetic157 (good-point/moving-center multiple-scale normalization anchor for finite-volume semialgebraic domains unpaid), Arithmetic155 (geometric control of the low places spendable by negative small diagrams in generalized-canonical Kähler fourfold flip sequences unpaid), Arithmetic154 (continuation of the quintic stability family through s=0 to the Gepner point unpaid), Arithmetic153 (geometric integrally marked gluing transport unpaid), Arithmetic152 (exact marked cancellation at the original exponent for b≥302 unpaid), Arithmetic151 (global holomorphic correction outside Calabi–Yau-base cases unpaid), Arithmetic150, Structural186 (uniform mixed overlap/attachment control across distinct extensions unpaid), Structural185, Arithmetic149/148, Structural184 and Analytic177 remain PREFREEZE/no nominee at their exact gaps. No retry/general impossibility. "
    "Arithmetic156 (Source057 root-stack fundamental-group isomorphism for the four-factor diagonal-quadric eightfold), Arithmetic147, S183N, S182P, Analytic161/T337A161 and T366A166 are whole-scope PASS/TECHNICAL, correctness conditions DISCHARGED, ZERO count; no bodies admitted or desired-grade retries. S176A remains correctness INCOMPLETE and contribution TECHNICAL conditional on full correctness, condition UNDISCHARGED; no necessary repair/counterexample established. T054L136 remains UNRESOLVED_FULL_SCOPE_REPAIR and NEEDS_REPAIR/INCOMPLETE. "
    "All older full targets/dispositions remain immutable, including every chromatic splitting conjecture (strong, weak and filtered forms), chromatic fracture square and chromatic overlap L_{n−1}L_{K(n)}, K(n)- and E(n)-localization, Morava E-theory and Morava stabilizer group, Lubin–Tate and Gross–Hopkins duality, derived p-completion and descent exponent, Adams–Novikov and β-family, telescope and thick-subcategory scope (including Structural187's and Structural189's) encountered in eligible ORIGINAL history."
)

assert new[43].startswith("Your ONE developed family is confirmed SOURCE317")
new[43] = ("Your ONE developed family is confirmed SOURCE318: CHROMATIC SPLITTING: FILTRATIONS AND COUNTEREXAMPLES. FIVE canonical manuscript folders in catalogue order, EIGHTY-FIVE tree blobs: "
           "Filtered-chromatic-splitting-at-generic-primes (September-25; wrapper build/paper.tex of 918 bytes, preamble, references.bib, twelve section inputs under build/sections numbered 01–11 with two distinct 10-prefixed files, README, compiled PDF; seventeen blobs), "
           "The-height-three-chromatic-overlap-an-explicit-filtration-and-its-attachments (September-27; wrapper build/paper.tex of 1196 bytes, preamble, references.bib, thirteen section inputs numbered 01–12 with two distinct 12-prefixed files, README, compiled PDF; eighteen blobs), "
           "A-rational-obstruction-to-strong-chromatic-splitting-at-height-three (September-25; wrapper build/main.tex of 1057 bytes, preamble, unicode-mappings.tex, references.bib, ten numbered section inputs 01–10 and sections/wedge-obstruction.tex, README, SUPPORT-COVERAGE.md, compiled PDF; eighteen blobs), "
           "Failure-of-finite-assembly-for-a-chromatic-overlap-at-the-prime-three (September-25; wrapper build/paper.tex of 3051 bytes, macros.tex, references.bib, ten numbered section inputs 01–10, README, compiled PDF; fifteen blobs) and "
           "Counterexamples-to-weak-chromatic-splitting-sphere-kernels-and-descent-exponents (September-27; wrapper build/main.tex of 1122 bytes, preamble, references.bib, twelve section inputs numbered 01–04 and 06–13, README, compiled PDF; seventeen blobs). "
           "Parent infers nothing from filenames or numbering gaps; establish from each wrapper which inputs are actually included and in what order, and from the bodies what each manuscript states and proves and how the five manuscripts depend on one another. Authenticate ALL eighty-five blobs; read actual FULL statements and ALL operative includes/required companions, strongest actual primary versions and relevant operative ORIGINAL history mechanisms BEFORE extended deductions or author drafting; disclose exactly which sections were not semantically read. "
           "Source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Validate new deductions/applicability, never audit source truth because it refutes or refines a previously open conjecture.")

assert new[45] == "Confirmed canonical wrapper at immutable pin:" and new[46].startswith("preprints/Thomason") and new[47].startswith("bytes3804")
wrapper_lines = ["Confirmed canonical wrappers at immutable pin:"]
for path, size, blob in WRAPS:
    wrapper_lines += [path, "bytes%d; Git blob%s." % (size, blob)]
new[45:48] = wrapper_lines  # 76 -> 84 lines
assert len(new) == 84
K = 8  # index shift for everything after the wrapper block

assert new[49 + K].startswith("Follow actual nested includes")
new[49 + K] = (
    "Follow actual nested includes/ancestors and complete-tree same-family objects, including every preamble, macro, unicode-mapping and section input and each bibliography actually included by its wrapper, and the SUPPORT-COVERAGE note; no guessed wrapper and no inference of a section's content from its filename or number. "
    "The source already proves, per catalogue: strong chromatic splitting fails at height three for every prime p≥5 (the canonical map L_0L_{K(3)}S→L_0L_{K(2)}L_{K(3)}S is nonzero on π_{−3}, so the height-three strong splitting formula fails even as an equivalence of underlying E(2)-local spectra); weak chromatic splitting fails for the derived p-completed sphere at height p for p≥5 and at height p+1 for p≥7, with β_1^{(p−1)²} a nonzero kernel class; for every n≥1 and p>n+1 the overlap L_{n−1}L_{K(n)}S_p^∧ admits a 2^n-stage ordered filtration by the classical chromatic-splitting cofibers whose first-stage map is the localization unit; for p≥5 an explicit eight-stage filtration of L_2L_{K(3)}S_p^∧ with two signed fracture formulas identifying all attachments and a nonzero first height-one attachment; and at p=3, height three, the overlap cannot be built from the rational, height-one and height-two local spheres by finitely many sums, shifts, cofibers and retracts in E(2)-local modules over the derived 3-complete sphere. "
    "These headlines, the fracture, tower, analytic, coheight-one, descent, integral, rational-boundary, Witt-transfer, Frobenius, oriented-projection, cooperation, coherent-trace and exponent constructions as the bodies actually perform them, the classical Hopkins/Hovey chromatic-splitting formulations, Morava E-theory, stabilizer-group cohomology, Gross–Hopkins, Devinatz–Hopkins and Adams–Novikov inputs as the bodies actually use them, and any compiled case analyses are paid, not nominees. "
    "Read the actual mechanism (which completion and localization functors are meant with their exact conventions, how each filtration stage and attachment is defined and detected, where p>n+1, p≥5, p≥7 and p=3 are each used, how the π_{−3} class and the β_1 power are detected, how finite assembly is formalized and obstructed, which statements are about underlying spectra versus modules with specified maps, and which classical results are inputs versus outputs), the exact definitions and conventions in each manuscript, and any limitation, non-uniqueness or open-case statements the sources themselves contain. "
    "Do NOT infer statements for primes or heights outside the stated ranges, for p≤n+1, for other localized spheres or finite complexes, for uniqueness or canonicity of the filtrations beyond what is stated, for finite assembly at other primes or heights, for strong or weak splitting in ranges not treated, for telescope-type or other conjectures, for Picard, duality or Hopf-algebroid consequences, or for explicit exponent or torsion bounds, from the proved statements. Stipulate every source operation rather than rejecting the headlines by older partial results."
)

assert new[51 + K].startswith("Develop a DISTINCT")
new[51 + K] = new[51 + K].replace("source nerve-detection/subdivision/attachment/presentability mechanisms", "source fracture/filtration/tower/descent-exponent mechanisms")
new[51 + K] = new[51 + K].replace("routine dimension, nerve or shape substitutions, unsupported extension to weak, non-globular, enriched or (∞,n)-categorical settings, other Ex counts or other base categories, homotopy-hypothesis or coherator consequences, unsupported explicit bounds or uniformity claims",
                                  "routine prime, height or spectrum substitutions, unsupported extension to small primes, other heights or other localized spheres and finite complexes, finite-assembly or splitting statements in ranges the sources do not treat, telescope-type, Picard or duality consequences, unsupported explicit bounds or uniformity claims")
assert "fracture/filtration/tower" in new[51 + K] and "small primes, other heights" in new[51 + K]

text = "\n".join(new)
for bad in ["r193-brief", "SOURCE317", "539611", "Thomason-Model", "8c9f165f", "bytes3804", "THIRTEEN", "*structural*r193* before", "fresh-structural-discovery-r192/", "discovery-structural-r192-parent", "Arithmetic160 (Source062", "nerve-detection", "lean/docs/317", "Ara–Maltsiniotis", "Street nerve", "Confirmed canonical wrapper at"]:
    assert bad not in text, bad
assert text.count("Thomason") == 1 and "Thomason" in new[41] and text.count("Gray") == 1
assert "fresh-structural-discovery-r194/" in text and "[540867,544391)" in text and "*arithmetic*r162*" in text and "*structural*r194*" in text and "*arithmetic*r163*" in text
assert sum(1 for l in new if l.startswith("preprints/")) == 5 and sum(1 for l in new if l.startswith("bytes")) == 5
out = os.path.join(ET, "fresh-structural-r194-brief.txt")
assert not os.path.exists(out)
open(out, "w", encoding="utf-8").write(text)
raw = open(out, "rb").read()
BRIEF_SHA, BRIEF_BYTES = sha(raw), len(raw)

json.dump({
    "observed_utc": NOW,
    "before_structural194_root_and_brief_dispatch": True,
    "live_peers_at_composition": "Arithmetic162 (Source064, idx651, dispatched by parent thread 6742db91-d35c-44d0-a762-e5d9232f5177 at commit 2789cbceb8) running, not inspected or steered; sole active peer at composition (ledger re-read immediately before composing)",
    "mutual_guards": {"this_brief_contains": "*arithmetic*r162* (supplement line) and the explicit peer-namespace exclusion including *owner-recovery*; prospective *arithmetic*r163*..r165*, *structural*r198*..r200*, *analytic*r190*..r192* added",
                      "peer_brief_contains": "*structural*r194* (supplement line of the original Arithmetic162 brief, SHA256 0b1098cdeea4bb53a3c85ced04f729f5480fff10c5c89354bde20213b5e46fc9) and the inherited explicit exclusion of unopened structural rounds"},
    "closed_round_excluded": {"Arithmetic156": "CLOSED PASS/TECHNICAL zero count; namespace excluded from broad selection; no bodies admitted"},
    "no_live_body_status_activity_or_findings_read": True,
    "completed_inputs_read_by_parent_before_brief": [
        "discovery-structural-r193-parent/assessment.md (parent-authored)",
        "fresh-structural-discovery-r193/FINAL.md, REPORT.md, DERIVATIONS.md, COMPARISON.md, ANCHORS.json, verify_packet.py, private/READING-LIMITS.md excerpts and private record schemas (at the r193 intake)",
    ],
    "limits": "Initial prompt chronology, not OS/perfect isolation.",
    "new_root_created_after_initial_guards_and_before_dispatch": True,
    "new_brief": {"path": "expanded-target-2026-10-17/fresh-structural-r194-brief.txt", "sha256": BRIEF_SHA, "bytes": BRIEF_BYTES, "lines": 84},
    "prospective_guard_supplement_in_brief": "extended: *arithmetic*r160*..r165*, *structural*r195*..r200*, *analytic*r187*..r192*; plus the no-r wildcard-twin instruction and the pre-traversal policy-comparison instruction naming *k369r134-* and *t185r144-*",
    "completed_exceptions_granted": "r193 FINAL/INTERFACES/DERIVATIONS/COMPARISON/READING-LIMITS and parent assessment; r192 exceptions withdrawn (unrelated stable-Hurewicz family, listed with its unpaid operation)",
    "source318_preparation": {
        "one_family": True,
        "catalogue_extent": list(EXT),
        "catalogue_sha256": BODY_SHA,
        "next_header_located_by_one_bounded_4000_byte_seek": True,
        "incidental_catalogue_display": "319 title and opening words displayed in the bounded window as navigation only",
        "title_only_navigation_range": [300, 320],
        "canonical_objects": 85,
        "canonical_folders": 5,
        "tree_entries": 95,
        "wrappers": [{"path": p, "bytes": s, "git_blob": g} for p, s, g in WRAPS],
        "lean_docs_link": False,
        "parent_read_source_proofs": False,
    },
}, open(os.path.join(HERE, "prospective-isolation.json"), "w"), indent=1)

root = os.path.join(C, "fresh-structural-discovery-r194")
os.mkdir(root)
print(json.dumps({"brief_sha256": BRIEF_SHA, "brief_bytes": BRIEF_BYTES, "lines": len(new), "root": root, "title320": title320, "body_sha256": BODY_SHA}))
