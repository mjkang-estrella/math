#!/usr/bin/env python3
"""Compose the Structural190 brief from the Structural189 brief and write the
Source314 navigation records for the Structural189 parent intake."""
import datetime
import hashlib
import json
import os
import shutil

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROJ = os.path.dirname(os.path.dirname(os.path.dirname(C)))
HERE = os.path.dirname(os.path.abspath(__file__))
PRIV = os.path.join(HERE, "private")
os.makedirs(PRIV, exist_ok=True)
NOW = datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha(b):
    return hashlib.sha256(b).hexdigest()


# --- Source314 catalogue body and navigation -------------------------------
EXT = (536770, 537826)
with open(os.path.join(PROJ, "sources/CONTENTS.md"), "rb") as f:
    f.seek(EXT[0])
    body = f.read(EXT[1] - EXT[0])
    f.seek(EXT[1])
    nxt = f.read(4000)
assert body.startswith(b"**314. Cyclic length and chromatic fixed-point loss.**")
assert nxt.startswith(b"**315. The four-dimensional Singer conjecture.**")
i316 = nxt.find(b"**316. ")
assert i316 >= 0
BODY_SHA = sha(body)
assert BODY_SHA == "e977b7e5521bfe747445dfc094c8837a3e5409a89534dd5eacdec3f6ae9f2665"
with open(os.path.join(PRIV, "catalogue-314.md"), "wb") as f:
    f.write(body)

nav_src = os.path.join(C, "discovery-structural-r188-parent/private/title-navigation.json")
nav = json.load(open(nav_src))
assert nav["families_selected"][-1] == {"family": 313, "round": "structural189"}
title316 = nxt[i316:nxt.find(b".**", i316) + 3].decode()
nav["numeric_range"] = [300, 316]
nav["titles"].append({"family": 316, "start": EXT[1] + i316,
                      "title_end": EXT[1] + i316 + len(title316.encode()),
                      "raw": title316})
nav["families_selected"].append({"family": 314, "round": "structural190"})
nav["next_header"] = {"family": 315, "start": EXT[1],
                      "located_by": "one bounded 4000-byte seek after 536770; body [536770,537826) decoded once for structural190 selection; 316 header located in the same bounded window"}
json.dump(nav, open(os.path.join(PRIV, "title-navigation.json"), "w"), indent=1)

# --- folder metadata --------------------------------------------------------
tree = json.load(open(os.path.join(PROJ, "sources/preprints-tree.json")))["tree"]
assert len(tree) == 13223
PRE = "preprints/Cyclic-Length-and-Chromatic-Fixed-Point-Loss-September-24-2026/"
fam = [e for e in tree if e["path"].startswith(PRE)]
blobs = [e for e in fam if e["type"] == "blob"]
assert len(fam) == 16 and len(blobs) == 13, (len(fam), len(blobs))
wrap = [e for e in blobs if e["path"] == PRE + "build/paper.tex"][0]
assert wrap["size"] == 771 and wrap["sha"] == "b4df60acc2debe29d4750cdb85255bce74130bc5"
others = [e["path"] for e in tree if "cyclic-length" in e["path"].lower() and not e["path"].startswith(PRE.rstrip("/"))]
assert not others, others
json.dump({
    "family": 314,
    "catalogue_extent": list(EXT),
    "catalogue_sha256": BODY_SHA,
    "next_header_confirmed": "**315. ... at 537826 (title decoded in the same bounded window; 316 header at %d)" % (EXT[1] + i316),
    "folders": [PRE.rstrip("/")],
    "blobs_per_folder": [13],
    "total_blobs": 13,
    "tree_entries": 16,
    "candidate_top_level_tex": ["build/paper.tex (771 B, blob b4df60acc2debe29d4750cdb85255bce74130bc5)"],
    "parent_read_source_proofs": False,
}, open(os.path.join(PRIV, "source314-selection.json"), "w"), indent=1)

# --- prospective isolation ---------------------------------------------------
ET = os.path.join(C, "expanded-target-2026-10-17")
peers = []
for idx, label, b in [
    (641, "Arithmetic156 proof review r1 (running)", "arithmetic-r156-proof-r1-brief.txt"),
    (642, "Arithmetic156 contribution review r1 (running)", "arithmetic-r156-contribution-r1-brief.txt"),
]:
    d = open(os.path.join(ET, b), "rb").read()
    assert b"*structural*r190*" in d
    peers.append({"task_index": idx, "label": label,
                  "brief": "expanded-target-2026-10-17/" + b,
                  "sha256": sha(d), "literal_existing_exclusion": "*structural*r190*"})

# --- brief --------------------------------------------------------------------
old = open(os.path.join(ET, "fresh-structural-r189-brief.txt"), encoding="utf-8").read().split("\n")
new = list(old)
assert new[0].startswith("Structural discovery r189")
new[0] = "Structural discovery r190 — confirmed cyclic-length chromatic fixed-point-loss operative-proof discovery."
new[1] = "Write ONLY frontier/campaigns/2026-10-14/fresh-structural-discovery-r190/."

a = new[9].index("The ORIGINAL INITIAL briefs")
b = new[9].index("Exact COMPLETED exceptions do not widen containing directories.") + len("Exact COMPLETED exceptions do not widen containing directories.")
new[9] = new[9][:a] + (
    "The ORIGINAL INITIAL briefs of both live Arithmetic156 review rounds already contain the literal prospective guard *structural*r190* before this new brief/root existed. "
    "The Arithmetic156 round (its author root, both independent review roots and parent records) is the only current active peer: exclude the ENTIRE *arithmetic*r156* namespace and every body/parent/brief/copy/derivative/status/activity alias. "
    "Structural189, Arithmetic157, Arithmetic155, Structural188, Structural187, Arithmetic154, Arithmetic153, Structural186, Arithmetic152, Arithmetic151 and Arithmetic150 are COMPLETED PREFREEZE/no nominee and parent-archived; exclude every structural189, arithmetic157, arithmetic155, structural188, structural187, arithmetic154, arithmetic153, structural186, arithmetic152, arithmetic151 and arithmetic150 namespace from broad selection; only the exact COMPLETED exceptions below are direct reads. "
    "Own structural190 namespace remains excluded from broad authored-history scans; own files usable. No peer body/status/activity/summary/finding may be inspected, inferred or used as premise. Do not inspect or steer peers to certify supplied isolation. This is prompt chronology, not OS/perfect isolation. Exact COMPLETED exceptions do not widen containing directories."
) + new[9][b:]

assert new[39].startswith("Catalogue access for THIS round")
new[39] = ("Catalogue access for THIS round, if needed at all: ONLY direct binary seek/read sources/CONTENTS.md[536770,537826), confirmed exact Source314 body. "
           "Parent reused numeric-header TITLE-ONLY300–316, located the 315 header by one bounded 4000-byte seek after 536770 and selected ONLY this family; parent has NOT read source theorem/proof bodies. "
           "No child catalogue scan, heading locator, read_text/readlines/whole read_bytes/decode or extra family. Full-tree metadata predicates use casefolded FULL paths. Selector failure is disclosed, never authorization for a wider span.")

assert new[41].startswith("Read these exact COMPLETED originals")
new[41] = (
    "Read these exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/: discovery-structural-r189-parent/assessment.md; fresh-structural-discovery-r189/FINAL.md; fresh-structural-discovery-r189/INTERFACES.md; fresh-structural-discovery-r189/DERIVATIONS.md; fresh-structural-discovery-r189/COMPARISON.md; fresh-structural-discovery-r189/private/READING-LIMITS.md; and, solely because Structural187 developed a different chromatic/K(n)-local family (Source311), discovery-structural-r187-parent/assessment.md; fresh-structural-discovery-r187/FINAL.md; fresh-structural-discovery-r187/COMPARISON.md. These completed inputs admit no containing namespace or status/activity access. "
    "Structural189 remains PREFREEZE/no nominee: on Source313 (finite generation for the K(n)-local sphere) it pays finite matrix cochain quotients of the compact stabilizer complex whose cohomology inverse limit is the continuous cohomology, eventual canonical persistent images with a non-effective finite detector, a continuous k-linear contraction with projection/primitive continuity moduli as stopping data, an all-orders convergent chain-correction certificate and explicit relative pole-absorption thresholds from the normalized Cartier transfer and fixed Yoneda diagram; the source-specific effectively represented all-orders chain contraction (equivalently effective projection and primitive moduli) in the deformation-adic filtration after marking/residue descent remains unpaid, coherent Cartier stabilization is inapplicable to the semilinear complex and the Adams horizontal line controls a different tower. "
    "Structural187 remains PREFREEZE/no nominee: it pays a non-effective uniform finite-sampling reduction in Honda obstruction coordinates, the adjugate norm detector with its determinant weight, exact finite-precision orbit-ideal matrices and a maximal-primary Nakayama lifting certificate; effective sampling constants with controlled transfer to original deformation coordinates, or effective orbit-ideal lifting across every height stratum, remain unpaid, and its Source311 thick-tensor-ideal scope is not this family. "
    "Structural188 (collapse-preserving lift c_S θ̃=θ c_j for every freely adjoined coherator operation after globular-sum gluing unpaid), Arithmetic157 (good-point/moving-center multiple-scale normalization supplying a compact-normalized interior anchor for two-sided scaling closure of bounded-symmetry finite-volume domains unpaid), Arithmetic155 (geometric control of the low places spendable by negative small diagrams in generalized-canonical Kähler fourfold flip sequences unpaid), Arithmetic154 (continuation of the quintic stability family through s=0 to the Gepner point unpaid), Arithmetic153 (geometric integrally marked gluing transport unpaid), Arithmetic152 (exact marked cancellation at the original exponent for b≥302 unpaid), Arithmetic151 (global holomorphic correction outside Calabi–Yau-base cases unpaid), Arithmetic150, Structural186 (uniform mixed overlap/attachment control across distinct extensions unpaid), Structural185, Arithmetic149/148, Structural184 and Analytic177 remain PREFREEZE/no nominee at their exact gaps. No retry/general impossibility. "
    "Arithmetic147, S183N, S182P, Analytic161/T337A161 and T366A166 are whole-scope PASS/TECHNICAL, correctness conditions DISCHARGED, ZERO count; no bodies admitted or desired-grade retries. S176A remains correctness INCOMPLETE and contribution TECHNICAL conditional on full correctness, condition UNDISCHARGED; no necessary repair/counterexample established. T054L136 remains UNRESOLVED_FULL_SCOPE_REPAIR and NEEDS_REPAIR/INCOMPLETE. "
    "All older full targets/dispositions remain immutable, including every geometric fixed point/isotropy separation, chromatic fixed-point loss/blue-shift, Kuhn–Lloyd, equivariant stable homotopy/Mackey functor, finite p-group representation and character theory, Balmer spectrum/thick tensor ideal, K(n)-local/Morava E-theory/Lubin–Tate, Morava stabilizer group and continuous-cohomology, chromatic finiteness/finite-generation and Tate/profinite-completion scope encountered in eligible ORIGINAL history."
)

assert new[43].startswith("Your ONE developed family is confirmed SOURCE313")
new[43] = ("Your ONE developed family is confirmed SOURCE314: CYCLIC LENGTH AND CHROMATIC FIXED-POINT LOSS. ONE canonical manuscript folder, THIRTEEN tree blobs: wrapper build/paper.tex of 771 bytes, preamble, references.tex, seven section inputs under build/sections, one unicode-map input under build/tools, README and compiled PDF (three further tree entries are directories). "
           "Parent infers nothing from filenames. Authenticate ALL thirteen blobs; read actual FULL statements and ALL operative includes/required companions, strongest actual primary versions and relevant operative ORIGINAL history mechanisms BEFORE extended deductions or author drafting; disclose exactly which sections were not semantically read. "
           "Source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Validate new deductions/applicability, never audit source truth because it resolves a previously open question.")

assert new[46].startswith("preprints/Finite-generation")
new[46] = PRE + "build/paper.tex"
new[47] = "bytes771; Git blobb4df60acc2debe29d4750cdb85255bce74130bc5."

assert new[49].startswith("Follow actual nested includes")
new[49] = (
    "Follow actual nested includes/ancestors and complete-tree same-family objects, including every section, preamble, bibliography and tool input actually included by the wrapper; no guessed wrapper and no inference of a section's content from its filename. "
    "The source already proves, per catalogue: for a finite p-group G and a subgroup H, the optimal chromatic fixed-point loss from geometric H-fixed points to geometric G-fixed points equals the shortest length of a subnormal chain from H to G with cyclic quotients, at every prime and every nonnegative height, each quotient counting once regardless of order, with finite spectra witnessing sharpness; this resolves positively the equality proposed by Kuhn and Lloyd. "
    "These headlines, the Kuhn–Lloyd framework and reductions as actually invoked, the classical geometric fixed point/isotropy separation, blue-shift, character, congruence, profinite and gluing inputs as the bodies actually use them, and any compiled case analyses are paid, not nominees. "
    "Read the actual mechanism (how chromatic fixed-point loss is defined and which height-shift inequalities the bodies actually prove in each direction, where the cyclic quotients, the p-group hypothesis, the prime, the height and the subnormal chain are each used, how the lower bound and the sharpness witnesses are constructed, which finite spectra witness sharpness and how, and which classical results are inputs versus outputs), the exact definitions and conventions for geometric fixed points, chromatic height and loss in this manuscript, and any counterexample, non-uniformity or limitation statements the source itself contains. "
    "Do NOT infer statements for non-p-groups, compact Lie groups or profinite groups, for other equivariant localizations or Mackey-functor/global settings beyond what is stated, for explicit witnessing spectra, ranks or growth beyond those stated, for uniformity in p or height beyond the stated equality, for Balmer-spectrum, telescope, duality or Picard consequences, for other fixed-point functors (categorical, homotopy, Tate) unless the bodies prove them, or for finer structure than stated, from the proved statements. Stipulate every source operation rather than rejecting the headline by older partial results."
)

assert new[51].startswith("Develop a DISTINCT")
new[51] = new[51].replace("source finite-generation/continuous-cohomology/completion mechanisms", "source fixed-point-loss/subnormal-chain/sharpness mechanisms")
new[51] = new[51].replace("routine prime, height, degree or finite-spectrum substitutions, unsupported extension to non-finite spectra or other localizations, unsupported explicit rank/torsion/growth bounds or uniformity claims",
                          "routine prime, height, subgroup or finite-spectrum substitutions, unsupported extension to non-p-groups, compact Lie groups or other fixed-point functors, unsupported explicit witness, rank or growth bounds or uniformity claims")
assert "fixed-point-loss/subnormal-chain" in new[51] and "non-p-groups, compact Lie groups" in new[51]

text = "\n".join(new)
assert "Source313" not in new[43] and "Source313" not in new[49] and "Source313" not in new[39]
for bad in ["r189-brief", "SOURCE313", "535744", "536770)", "Finite-generation-for-the-Kn", "5a7c121c", "1682", "NINETEEN", "K(n)-LOCAL SPHERE", "Arithmetic157 already", "*structural*r189* before"]:
    assert bad not in text, bad
assert "fresh-structural-discovery-r190/" in text and "[536770,537826)" in text
out = os.path.join(ET, "fresh-structural-r190-brief.txt")
assert not os.path.exists(out)
open(out, "w", encoding="utf-8").write(text)
raw = open(out, "rb").read()
BRIEF_SHA, BRIEF_BYTES = sha(raw), len(raw)

json.dump({
    "observed_utc": NOW,
    "before_structural190_root_and_brief_dispatch": True,
    "existing_active_peer_original_initial_briefs": peers,
    "both_original_initial_guards_cover_entire_structural190_namespace": True,
    "no_live_Arithmetic156_review_body_status_activity_or_findings_read": True,
    "completed_inputs_read_by_parent_before_brief": [
        "fresh-structural-discovery-r189/FINAL.md",
        "fresh-structural-discovery-r189/REPORT.md",
        "fresh-structural-discovery-r189/DERIVATIONS.md",
        "fresh-structural-discovery-r189/COMPARISON.md",
        "fresh-structural-discovery-r189/ANCHORS.json",
        "fresh-structural-discovery-r189/SEAL-TESTS.json",
        "fresh-structural-discovery-r189/verify_packet.py",
        "fresh-structural-discovery-r189/INTERFACES.md (opening)",
        "fresh-structural-discovery-r189/private/READING-LIMITS.md (opening)",
    ],
    "limits": "Initial prompt chronology, not OS/perfect isolation.",
    "new_root_created_after_initial_guards_and_before_dispatch": True,
    "new_brief": {"path": "expanded-target-2026-10-17/fresh-structural-r190-brief.txt", "sha256": BRIEF_SHA, "bytes": BRIEF_BYTES},
    "prospective_guard_supplement_in_brief": "carried: *arithmetic*r160*..r162*, *structural*r195*..r197*, *analytic*r187*..r189* (no new line needed; structural headroom through r197)",
    "completed_exceptions_granted": "r189 FINAL/INTERFACES/DERIVATIONS/COMPARISON/READING-LIMITS and parent assessment; additionally r187 assessment/FINAL/COMPARISON because Structural187 developed a different chromatic/K(n)-local family (Source311); r188 excluded (unrelated homotopy-hypothesis family)",
    "source314_preparation": {
        "one_family": True,
        "catalogue_extent": list(EXT),
        "catalogue_sha256": BODY_SHA,
        "next_header_located_by_one_bounded_4000_byte_seek": True,
        "title_only_navigation_range": [300, 316],
        "canonical_objects": 13,
        "canonical_folders": 1,
        "tree_entries": 16,
        "lean_docs_link": False,
        "parent_read_source_proofs": False,
    },
}, open(os.path.join(HERE, "prospective-isolation.json"), "w"), indent=1)

root = os.path.join(C, "fresh-structural-discovery-r190")
os.mkdir(root)
print(json.dumps({"brief_sha256": BRIEF_SHA, "brief_bytes": BRIEF_BYTES, "root": root, "title316": title316}))
