#!/usr/bin/env python3
"""Compose the Structural192 brief from the Structural191 brief and write the
Source316 navigation records for the Structural191 parent intake."""
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


# --- Source316 catalogue body and navigation -------------------------------
EXT = (538801, 539611)
with open(os.path.join(PROJ, "sources/CONTENTS.md"), "rb") as f:
    f.seek(EXT[0])
    body = f.read(EXT[1] - EXT[0])
    f.seek(EXT[1])
    nxt = f.read(4000)
assert body.startswith(b"**316. Curtis\xe2\x80\x99s conjecture.**")
assert nxt.startswith(b"**317. Thomason model structures in all strict higher dimensions.**")
i318 = nxt.find(b"**318. ")
assert i318 >= 0
assert b"lean/docs" not in body
BODY_SHA = sha(body)
assert BODY_SHA == "113ede9ea826e5d72a8869e308ee0feb2a3df379f4e722a331de936d25dca83a"
with open(os.path.join(PRIV, "catalogue-316.md"), "wb") as f:
    f.write(body)

nav_src = os.path.join(C, "discovery-structural-r190-parent/private/title-navigation.json")
nav = json.load(open(nav_src))
assert nav["families_selected"][-1] == {"family": 315, "round": "structural191"}
assert nav["next_header"]["family"] == 316 and nav["next_header"]["start"] == EXT[0]
title318 = nxt[i318:nxt.find(b".**", i318) + 3].decode()
nav["numeric_range"] = [300, 318]
nav["titles"].append({"family": 318, "start": EXT[1] + i318,
                      "title_end": EXT[1] + i318 + len(title318.encode()),
                      "raw": title318})
nav["families_selected"].append({"family": 316, "round": "structural192"})
nav["next_header"] = {"family": 317, "start": EXT[1],
                      "located_by": "317 header located earlier in the bounded window after 538801; body [538801,539611) decoded once for structural192 selection; 318 header located by one bounded 4000-byte seek after 539611",
                      "incidental_display": "the bounded window after 539611 displayed the 317 title and opening abstract words to the parent as navigation only; no source theorem/proof body was read and no family other than 316 was selected"}
json.dump(nav, open(os.path.join(PRIV, "title-navigation.json"), "w"), indent=1)

# --- folder metadata --------------------------------------------------------
tree = json.load(open(os.path.join(PROJ, "sources/preprints-tree.json")))["tree"]
assert len(tree) == 13223
PRE = "preprints/The-Stable-Hurewicz-Image-of-the-Sphere-at-Two-September-25-2026/"
assert body.decode().count("](preprints/") == 1 and PRE[len("preprints/"):] + "paper.pdf" in body.decode()
fam = [e for e in tree if e["path"].startswith(PRE)]
blobs = [e for e in fam if e["type"] == "blob"]
assert len(fam) == 14 and len(blobs) == 12, (len(fam), len(blobs))
wrap = [e for e in blobs if e["path"] == PRE + "build/paper.tex"][0]
assert wrap["size"] == 762 and wrap["sha"] == "eb74588690f4" + wrap["sha"][12:]
WRAP_SHA = wrap["sha"]
names = sorted(e["path"][len(PRE):] for e in blobs)
assert names == ["README.md", "build/algebra.tex", "build/conclusion.tex", "build/cones.tex", "build/figures/proof-route.tex",
                 "build/introduction.tex", "build/paper.tex", "build/powers.tex", "build/preamble.tex", "build/references.bib",
                 "build/weights.tex", "paper.pdf"], names
others = [e["path"] for e in tree if "hurewicz" in e["path"].lower() and not e["path"].startswith(PRE.rstrip("/"))]
assert not others, others
json.dump({
    "family": 316,
    "catalogue_extent": list(EXT),
    "catalogue_sha256": BODY_SHA,
    "next_header_confirmed": "**317. Thomason model structures in all strict higher dimensions.** at 539611 (located earlier); 318 header at %d" % (EXT[1] + i318),
    "folders": [PRE.rstrip("/")],
    "blobs_per_folder": [12],
    "total_blobs": 12,
    "tree_entries": 14,
    "candidate_top_level_tex": ["build/paper.tex (762 B, blob %s)" % WRAP_SHA],
    "blob_names_only": names,
    "lean_docs_link": False,
    "parent_read_source_proofs": False,
}, open(os.path.join(PRIV, "source316-selection.json"), "w"), indent=1)

# --- brief --------------------------------------------------------------------
ET = os.path.join(C, "expanded-target-2026-10-17")
old = open(os.path.join(ET, "fresh-structural-r191-brief.txt"), encoding="utf-8").read().split("\n")
assert len(old) == 76
new = list(old)
assert new[0].startswith("Structural discovery r191")
new[0] = "Structural discovery r192 — confirmed Curtis conjecture (mod-two stable Hurewicz image of the sphere) operative-proof discovery."
new[1] = "Write ONLY frontier/campaigns/2026-10-14/fresh-structural-discovery-r192/."

a = new[9].index("The ORIGINAL INITIAL brief of Arithmetic158")
b = new[9].index("Exact COMPLETED exceptions do not widen containing directories.") + len("Exact COMPLETED exceptions do not widen containing directories.")
new[9] = new[9][:a] + (
    "The ORIGINAL INITIAL brief of Arithmetic159, dispatched before this round, contains the literal prospective guard *structural*r192* before any structural192 body existed, and this brief contains *arithmetic*r159* while arithmetic159 is live. "
    "Arithmetic159 (Source060, its author root and parent records) is the only current active peer: exclude the ENTIRE *arithmetic*r159* namespace and every body/parent/brief/copy/derivative/status/activity alias. "
    "Arithmetic156 is COMPLETED and CLOSED whole-scope PASS/TECHNICAL with ZERO count (its author root, both review roots and parent records are no longer live): exclude the ENTIRE *arithmetic*r156* namespace from broad selection; no bodies admitted. "
    "Structural191, Arithmetic158, Structural190, Structural189, Arithmetic157, Arithmetic155, Structural188, Structural187, Arithmetic154, Arithmetic153, Structural186, Arithmetic152, Arithmetic151 and Arithmetic150 are COMPLETED PREFREEZE/no nominee and parent-archived; exclude every structural191, arithmetic158, structural190, structural189, arithmetic157, arithmetic155, structural188, structural187, arithmetic154, arithmetic153, structural186, arithmetic152, arithmetic151 and arithmetic150 namespace from broad selection; only the exact COMPLETED exceptions below are direct reads. "
    "Also exclude every full-path alias of a completed or live round that lacks the literal r (for example arithmetic151-stopped.json style status aliases, arithmetic15N*, structural19N*, analytic18N*) by installing the no-r wildcard twins of every listed guard before traversal. "
    "Own structural192 namespace remains excluded from broad authored-history scans; own files usable. No peer body/status/activity/summary/finding may be inspected, inferred or used as premise. Do not inspect or steer peers to certify supplied isolation. This is prompt chronology, not OS/perfect isolation. Exact COMPLETED exceptions do not widen containing directories."
) + new[9][b:]

assert new[39].startswith("Catalogue access for THIS round")
new[39] = ("Catalogue access for THIS round, if needed at all: ONLY direct binary seek/read sources/CONTENTS.md[538801,539611), confirmed exact Source316 body. "
           "Parent reused numeric-header TITLE-ONLY300–317, located the 318 header by one bounded 4000-byte seek after 539611 (that window displayed the 317 title and opening abstract words to the parent as navigation only) and selected ONLY this family; parent has NOT read source theorem/proof bodies. The body links no Lean documentation page. "
           "No child catalogue scan, heading locator, read_text/readlines/whole read_bytes/decode or extra family. Full-tree metadata predicates use casefolded FULL paths. Selector failure is disclosed, never authorization for a wider span.")

assert new[41].startswith("Read these exact COMPLETED originals")
new[41] = (
    "Read these exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/: discovery-structural-r191-parent/assessment.md; fresh-structural-discovery-r191/FINAL.md; fresh-structural-discovery-r191/INTERFACES.md; fresh-structural-discovery-r191/DERIVATIONS.md; fresh-structural-discovery-r191/COMPARISON.md; fresh-structural-discovery-r191/private/READING-LIMITS.md. These completed inputs admit no containing namespace or status/activity access; Structural190, Structural189 and Structural187 (finite p-group and K(n)-local/chromatic families) are unrelated to this family and admit no exceptions. "
    "Structural191 remains PREFREEZE/no nominee: on Source315 (the four-dimensional Singer conjecture for finite aspherical integral Poincaré complexes) it pays exact rational finite-support least-squares witnesses with residual tending to zero by source L²-vanishing, an exact finite regular-cover Betti certificate with nonorientable duality accounting, the norm-cost spectral inequality with its exact regularized minimizer, the paid Clair–Whyte Chebyshev construction and Lück logarithmic bound, a finite-propagation inverse truncation, a cap-product finite-support correction with its filling-radius dependence, and a compatibility comparison with the source's all-representative depth and three-anchor path refinement; a full-scope construction of the same finite-support columns with simultaneous power-decay residual and power-growth norm bounds, or an equally strong closed geometric substitute, remains unpaid, and its L²-invariant scope is not this family. "
    "Arithmetic158 (vanishing of the once-squared determinant class in T(A_f)/(T(Q)det K) with saturated 2-torsion and conductor residues at 3,5,7,11,13 unpaid), Structural190 (structural finite-precision elimination or global chain exchange with an a priori stabilization bound for cyclic lengths of finite p-group products unpaid), Structural189 (source-specific effectively represented all-orders chain contraction in the deformation-adic filtration unpaid), Structural188 (collapse-preserving lift c_S θ̃=θ c_j for every freely adjoined coherator operation after globular-sum gluing unpaid), Structural187 (effective sampling constants/coordinate transfer or all-strata orbit-ideal lifting unpaid), Arithmetic157 (good-point/moving-center multiple-scale normalization anchor for finite-volume semialgebraic domains unpaid), Arithmetic155 (geometric control of the low places spendable by negative small diagrams in generalized-canonical Kähler fourfold flip sequences unpaid), Arithmetic154 (continuation of the quintic stability family through s=0 to the Gepner point unpaid), Arithmetic153 (geometric integrally marked gluing transport unpaid), Arithmetic152 (exact marked cancellation at the original exponent for b≥302 unpaid), Arithmetic151 (global holomorphic correction outside Calabi–Yau-base cases unpaid), Arithmetic150, Structural186 (uniform mixed overlap/attachment control across distinct extensions unpaid), Structural185, Arithmetic149/148, Structural184 and Analytic177 remain PREFREEZE/no nominee at their exact gaps. No retry/general impossibility. "
    "Arithmetic156 (Source057 root-stack fundamental-group isomorphism for the four-factor diagonal-quadric eightfold), Arithmetic147, S183N, S182P, Analytic161/T337A161 and T366A166 are whole-scope PASS/TECHNICAL, correctness conditions DISCHARGED, ZERO count; no bodies admitted or desired-grade retries. S176A remains correctness INCOMPLETE and contribution TECHNICAL conditional on full correctness, condition UNDISCHARGED; no necessary repair/counterexample established. T054L136 remains UNRESOLVED_FULL_SCOPE_REPAIR and NEEDS_REPAIR/INCOMPLETE. "
    "All older full targets/dispositions remain immutable, including every stable homotopy groups of spheres, Adams and Adams–Novikov spectral sequence, Steenrod algebra and Ext computation, Lambda algebra, Hurewicz image and Hurewicz homomorphism, Hopf invariant one, Kervaire invariant, Mahowald/Curtis/Eccles conjecture, Brown–Gitler spectrum, root invariant, Thom spectrum and bordism, infinite loop space homology and Dyer–Lashof operation scope encountered in eligible ORIGINAL history."
)

assert new[43].startswith("Your ONE developed family is confirmed SOURCE315")
new[43] = ("Your ONE developed family is confirmed SOURCE316: CURTIS'S CONJECTURE. ONE canonical manuscript folder, TWELVE tree blobs: wrapper build/paper.tex of 762 bytes, build/preamble.tex, six further .tex inputs directly under build/ (algebra, conclusion, cones, introduction, powers, weights), one figure input build/figures/proof-route.tex, references.bib, README and compiled PDF (two further tree entries are the build and build/figures directories). "
           "Parent infers nothing from filenames; establish from the wrapper which inputs are actually included and in what order, and from the bodies what each section states and proves and how the figure input is used. Authenticate ALL twelve blobs; read actual FULL statements and ALL operative includes/required companions, strongest actual primary versions and relevant operative ORIGINAL history mechanisms BEFORE extended deductions or author drafting; disclose exactly which sections were not semantically read. "
           "Source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Validate new deductions/applicability, never audit source truth because it resolves a previously open conjecture.")

assert new[46].startswith("preprints/The-Singer-conjecture")
new[46] = PRE + "build/paper.tex"
new[47] = "bytes762; Git blob%s." % WRAP_SHA

assert new[49].startswith("Follow actual nested includes")
new[49] = (
    "Follow actual nested includes/ancestors and complete-tree same-family objects, including every .tex input, the preamble, the figure input and the bibliography actually included by the wrapper; no guessed wrapper and no inference of a section's content from its filename. "
    "The source already proves, per catalogue: Curtis's conjecture, that in every positive degree the mod-two stable Hurewicz image of the sphere is spanned by the images of the Hopf-invariant-one classes η, ν, σ and the Kervaire-invariant-one classes that exist; consequently Eccles's conjecture holds for every sphere S^n with n>0. "
    "These headlines, the algebraic, weight, power and cone constructions as the bodies actually perform them, the classical Adams spectral sequence, Steenrod-algebra, Hopf-invariant-one, Kervaire-invariant, Dyer–Lashof/infinite-loop-space and Brown–Gitler/Mahowald inputs as the bodies actually use them, and any compiled case analyses are paid, not nominees. "
    "Read the actual mechanism (which Hurewicz homomorphism is meant, with its exact source and target, how the spanning classes are identified and shown to lie in the image, how every other class is shown to have zero Hurewicz image, where the prime two, positive degree, stability and the existence hypothesis on Kervaire classes are each used, how Eccles's conjecture is deduced and for which spaces, and which classical results are inputs versus outputs), the exact definitions and conventions in this manuscript, and any limitation, non-uniqueness or open-case statements the source itself contains. "
    "Do NOT infer statements for odd primes, for unstable Hurewicz images or other spaces and spectra beyond those stated, for Eccles-type statements on manifolds other than the stated spheres, for the existence or nonexistence of Kervaire-invariant-one classes beyond what is stated, for Mahowald's or other conjectures, for root invariants, bordism or immersion consequences, for explicit Adams filtration bounds, or for finer structure than stated, from the proved statements. Stipulate every source operation rather than rejecting the headline by older partial results."
)

assert new[51].startswith("Develop a DISTINCT")
new[51] = new[51].replace("source L²-vanishing/duality/boundary-dynamics mechanisms", "source Hurewicz-image/weight-filtration/algebraic mechanisms")
new[51] = new[51].replace("routine dimension, coefficient or group-class substitutions, unsupported extension to higher dimensions, non-aspherical or non-finite complexes, Hopf/Atiyah/L²-torsion consequences or other L²-invariants, unsupported explicit bounds or uniformity claims",
                          "routine prime, degree, space or spectrum substitutions, unsupported extension to odd primes, unstable or other-spectrum Hurewicz images, Eccles-type statements for other manifolds, Kervaire-existence or Mahowald-type consequences, unsupported explicit bounds or uniformity claims")
assert "Hurewicz-image/weight-filtration/algebraic" in new[51] and "odd primes, unstable" in new[51]

text = "\n".join(new)
assert len(new) == 76
for bad in ["r191-brief", "SOURCE315", "537826", "Singer-conjecture-in", "58c43c1b", "bytes1698", "SIXTEEN", "*structural*r191* before", "fresh-structural-discovery-r190/", "discovery-structural-r190-parent", "dispatched together with this round", "Arithmetic158 (Source059, its author root"]:
    assert bad not in text, bad
assert text.count("Singer") == 1 and "Singer" in new[41] and text.count("aspherical") == 1
assert "fresh-structural-discovery-r192/" in text and "[538801,539611)" in text and "*arithmetic*r159*" in text and "*structural*r192*" in text
out = os.path.join(ET, "fresh-structural-r192-brief.txt")
assert not os.path.exists(out)
open(out, "w", encoding="utf-8").write(text)
raw = open(out, "rb").read()
BRIEF_SHA, BRIEF_BYTES = sha(raw), len(raw)

json.dump({
    "observed_utc": NOW,
    "before_structural192_root_and_brief_dispatch": True,
    "live_peers_at_composition": "Arithmetic159 (Source060) running, not inspected or steered; sole active peer",
    "mutual_guards": {"this_brief_contains": "*arithmetic*r159* (supplement line, inherited) and the explicit peer-namespace exclusion",
                      "peer_brief_contains": "*structural*r192* (supplement line of the original Arithmetic159 brief) and the inherited explicit exclusion of unopened structural rounds"},
    "closed_round_excluded": {"Arithmetic156": "CLOSED PASS/TECHNICAL zero count; namespace excluded from broad selection; no bodies admitted"},
    "no_live_body_status_activity_or_findings_read": True,
    "completed_inputs_read_by_parent_before_brief": [
        "discovery-structural-r191-parent/assessment.md (parent-authored)",
        "fresh-structural-discovery-r191/FINAL.md, REPORT.md, DERIVATIONS.md, INTERFACES.md, COMPARISON.md, RESEARCH-NOTES.md, ANCHORS.json, verify_packet.py, private/READING-LIMITS.md (at the r191 intake)",
    ],
    "limits": "Initial prompt chronology, not OS/perfect isolation.",
    "new_root_created_after_initial_guards_and_before_dispatch": True,
    "new_brief": {"path": "expanded-target-2026-10-17/fresh-structural-r192-brief.txt", "sha256": BRIEF_SHA, "bytes": BRIEF_BYTES},
    "prospective_guard_supplement_in_brief": "carried: *arithmetic*r160*..r162*, *structural*r195*..r197*, *analytic*r187*..r189*; plus the no-r wildcard-twin instruction",
    "completed_exceptions_granted": "r191 FINAL/INTERFACES/DERIVATIONS/COMPARISON/READING-LIMITS and parent assessment; r190 exceptions withdrawn (unrelated finite p-group family)",
    "source316_preparation": {
        "one_family": True,
        "catalogue_extent": list(EXT),
        "catalogue_sha256": BODY_SHA,
        "next_header_located_by_one_bounded_4000_byte_seek": True,
        "incidental_catalogue_display": "317 title and opening abstract words displayed in the bounded window as navigation only",
        "title_only_navigation_range": [300, 318],
        "canonical_objects": 12,
        "canonical_folders": 1,
        "tree_entries": 14,
        "lean_docs_link": False,
        "parent_read_source_proofs": False,
    },
}, open(os.path.join(HERE, "prospective-isolation.json"), "w"), indent=1)

root = os.path.join(C, "fresh-structural-discovery-r192")
os.mkdir(root)
print(json.dumps({"brief_sha256": BRIEF_SHA, "brief_bytes": BRIEF_BYTES, "root": root, "title318": title318, "body_sha256": BODY_SHA, "wrap_sha": WRAP_SHA}))
