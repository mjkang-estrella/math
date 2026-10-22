#!/usr/bin/env python3
"""Compose the Arithmetic159 brief from the Arithmetic158 brief and write the
Source060 navigation records for the Arithmetic158 parent intake."""
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


# --- Source060 catalogue body and navigation -------------------------------
EXT = (106786, 107733)
with open(os.path.join(PROJ, "sources/CONTENTS.md"), "rb") as f:
    f.seek(EXT[0])
    probe = f.read(4000)
assert probe.find(b"**061. ") == -1  # numeric headers are not contiguous; 061 is absent
i062 = probe.find(b"**062. ")
assert i062 == EXT[1] - EXT[0], i062
body = probe[:i062]
nxt = probe[i062:]
assert body.startswith(b"**060. The Global Spherical Shell conjecture.**")
assert nxt.startswith(b"**062. ")
assert b"lean/docs" not in body
BODY_SHA = sha(body)
assert BODY_SHA == "e12dd05da731177b14393c723a1d2872ce78d7a0ff7cc3554ee0ce3dfae6548e"
with open(os.path.join(PRIV, "catalogue-060.md"), "wb") as f:
    f.write(body)
title062 = nxt[:nxt.find(b".**") + 3].decode()

nav_src = os.path.join(C, "discovery-arithmetic-r157-parent/private/title-navigation.json")
nav = json.load(open(nav_src))
assert nav["families_selected"]["059"] == "arithmetic158" and nav["next_header"]["family"] == 60
nav["numeric_range"] = [43, 62]
nav["titles"].append({"family": 60, "start": EXT[0], "title_end": None,
                      "raw": "**060. The Global Spherical Shell conjecture.**",
                      "how": "header located earlier by one bounded 4000-byte seek after 105150; body [106786,107733) decoded once for arithmetic159 selection"})
nav["families_selected"]["060"] = "arithmetic159"
nav["next_header"] = {"family": 62, "start": EXT[1], "raw": title062,
                      "located_by": "one bounded 4000-byte seek after 106786; no 061 header exists in that window (headers not contiguous); end not located",
                      "incidental_display": "the bounded window displayed catalogue title/abstract text of families 062-064 to the parent as navigation only; no source theorem/proof body was read and no family other than 060 was selected"}
json.dump(nav, open(os.path.join(PRIV, "title-navigation.json"), "w"), indent=1)

# --- folder metadata --------------------------------------------------------
tree = json.load(open(os.path.join(PROJ, "sources/preprints-tree.json")))["tree"]
assert len(tree) == 13223
F1 = "preprints/Global-Spherical-Shells-on-Minimal-Surfaces-of-Class-VII-September-24-2026/"
links = [l for l in body.decode().split("](preprints/")[1:]]
assert len(links) == 1 and links[0].startswith(F1[len("preprints/"):] + "paper.pdf")
fam1 = [e for e in tree if e["path"].startswith(F1)]
b1 = [e for e in fam1 if e["type"] == "blob"]
assert (len(fam1), len(b1)) == (14, 11), (len(fam1), len(b1))
w1 = [e for e in b1 if e["path"] == F1 + "build/paper.tex"][0]
assert w1["size"] == 16805 and w1["sha"] == "f79ccb59553aa128043c866d98f9b5a7ae4824b2"
names = sorted(e["path"][len(F1):] for e in b1)
assert names == ["README.md", "build/figures/flat-chain.tex", "build/paper.tex", "build/references.tex",
                 "build/sections/compact-data.tex", "build/sections/conclusion.tex", "build/sections/curves.tex",
                 "build/sections/cylinder.tex", "build/sections/surfaces.tex", "build/sections/weighted.tex", "paper.pdf"], names
others = [e["path"] for e in tree if "spherical-shell" in e["path"].lower() and not e["path"].startswith(F1.rstrip("/"))]
assert not others, others
json.dump({
    "family": 60,
    "catalogue_extent": list(EXT),
    "catalogue_sha256": BODY_SHA,
    "next_header_confirmed": "%s at %d (no 061 header; title decoded in the same bounded window)" % (title062, EXT[1]),
    "folders": [F1.rstrip("/")],
    "blobs_per_folder": [11],
    "total_blobs": 11,
    "tree_entries": [14],
    "candidate_top_level_tex": ["build/paper.tex (16805 B, blob f79ccb59553aa128043c866d98f9b5a7ae4824b2)"],
    "blob_names_only": names,
    "lean_docs_link": False,
    "parent_read_source_proofs": False,
}, open(os.path.join(PRIV, "source060-selection.json"), "w"), indent=1)

# --- brief --------------------------------------------------------------------
ET = os.path.join(C, "expanded-target-2026-10-17")
old = open(os.path.join(ET, "fresh-arithmetic-r158-brief.txt"), encoding="utf-8").read().split("\n")
assert len(old) == 78
new = list(old)
assert new[0].startswith("Arithmetic discovery r158")
new[0] = "Arithmetic discovery r159 — confirmed Global Spherical Shell (class VII, positive b₂) operative-proof discovery."
new[1] = "Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r159/."

a = new[9].index("The ORIGINAL INITIAL brief of Structural191")
b = new[9].index("Exact COMPLETED exceptions do not widen containing directories.") + len("Exact COMPLETED exceptions do not widen containing directories.")
new[9] = new[9][:a] + (
    "The ORIGINAL INITIAL brief of Structural191, dispatched before this round, contains the literal prospective guard *arithmetic*r159* before any arithmetic159 body existed, and this brief contains *structural*r191* while structural191 is live. "
    "Structural191 (Source315, its author root and parent records) is the only current active peer: exclude the ENTIRE *structural*r191* namespace and every body/parent/brief/copy/derivative/status/activity alias. "
    "Arithmetic156 is COMPLETED and CLOSED whole-scope PASS/TECHNICAL with ZERO count (its author root, both review roots and parent records are no longer live): exclude the ENTIRE *arithmetic*r156* namespace from broad selection; no bodies admitted. "
    "Arithmetic158, Structural190, Structural189, Arithmetic157, Arithmetic155, Structural188, Structural187, Arithmetic154, Arithmetic153, Structural186, Arithmetic152, Arithmetic151 and Arithmetic150 are COMPLETED PREFREEZE/no nominee and parent-archived; exclude every arithmetic158, structural190, structural189, arithmetic157, arithmetic155, structural188, structural187, arithmetic154, arithmetic153, structural186, arithmetic152, arithmetic151 and arithmetic150 namespace from broad selection; only the exact COMPLETED exceptions below are direct reads. "
    "Also exclude every full-path alias of a completed or live round that lacks the literal r (for example arithmetic151-stopped.json style status aliases, arithmetic15N*, structural19N*, analytic18N*) by installing the no-r wildcard twins of every listed guard before traversal. "
    "Own arithmetic159 namespace remains excluded from broad authored-history scans; own files usable. No peer body/status/activity/summary/finding may be inspected, inferred or used as premise. Do not inspect or steer peers to certify supplied isolation. This is prompt chronology, not OS/perfect isolation. Exact COMPLETED exceptions do not widen containing directories."
) + new[9][b:]

assert new[39].startswith("Catalogue access for THIS round")
new[39] = ("Catalogue access for THIS round, if needed at all: ONLY direct binary seek/read sources/CONTENTS.md[106786,107733), confirmed exact Source060 body. "
           "Parent reused numeric-header TITLE-ONLY43–60, located the 062 header by one bounded 4000-byte seek after 106786 (no 061 header exists; numeric headers are not contiguous) and selected ONLY this family; the bounded window displayed catalogue title/abstract text of families 062–064 to the parent as navigation only; parent has NOT read source theorem/proof bodies. The body links no Lean documentation page. "
           "No child catalogue scan, heading locator, read_text/readlines/whole read_bytes/decode or extra family. Full-tree metadata predicates use casefolded FULL paths. Selector failure is disclosed, never authorization for a wider span.")

assert new[41].startswith("Read these exact COMPLETED originals")
new[41] = (
    "Read these exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/: discovery-arithmetic-r158-parent/assessment.md; fresh-arithmetic-discovery-r158/packet/FINAL.md; fresh-arithmetic-discovery-r158/packet/notes/01-operative-comparison.md; fresh-arithmetic-discovery-r158/packet/notes/02-once-squared-reduction.md; fresh-arithmetic-discovery-r158/packet/notes/03-conductor-and-cancellation.md; fresh-arithmetic-discovery-r158/packet/private/READING-ISOLATION.md. These completed inputs admit no containing namespace or status/activity access. "
    "Arithmetic158 remains PREFREEZE/no nominee: on Source059 (counterexamples to Zariski's multiplicity conjecture) it pays the reduction of an integral equivariant isometry of the once-squared lattices to the vanishing of a determinant class χ in T(A_f)/(T(Q)·det K) with the determinant-one part paid by strong approximation, the 2-torsion control of the saturated image of χ from the source monodromy-module isomorphism, and the Ramanujan-sum conductor m=3¹²·5·7·11·13 with local conductors and Kirschmer's local determinant theorem; the vanishing of χ in the full quotient (saturated 2-torsion and the conductor residue class at 3, 5, 7, 11, 13) for every admissible relation, or complementary marked splittings on the once-squared lattice, remains unpaid, and its singularity-topology scope is not this family. "
    "Structural190 (structural finite-precision elimination or global chain exchange with an a priori stabilization bound for cyclic lengths of finite p-group products unpaid), Structural189 (source-specific effectively represented all-orders chain contraction in the deformation-adic filtration unpaid), Arithmetic157 (good-point/moving-center multiple-scale normalization anchor for finite-volume semialgebraic domains unpaid), Arithmetic155 (geometric control of the low places spendable by negative small diagrams in generalized-canonical Kähler fourfold flip sequences unpaid), Structural188 (collapse-preserving lift c_S θ̃=θ c_j for every freely adjoined coherator operation unpaid), Structural187 (effective sampling constants/coordinate transfer or all-strata orbit-ideal lifting unpaid), Arithmetic154 (continuation of the quintic stability family through s=0 to the Gepner point unpaid), Arithmetic153 (geometric integrally marked gluing transport unpaid), Arithmetic152 (exact marked cancellation at the original exponent for b≥302 unpaid), Arithmetic151 (global holomorphic correction outside Calabi–Yau-base cases unpaid), Arithmetic150, Structural186 (uniform mixed overlap/attachment control across distinct extensions unpaid), Structural185, Arithmetic149/148, Structural184 and Analytic177 remain PREFREEZE/no nominee at their exact gaps. No retry/general impossibility. "
    "Arithmetic156 (Source057 root-stack fundamental-group isomorphism for the four-factor diagonal-quadric eightfold), Arithmetic147, S183N, S182P, Analytic161/T337A161 and T366A166 are whole-scope PASS/TECHNICAL, correctness conditions DISCHARGED, ZERO count; no bodies admitted or desired-grade retries. S176A remains correctness INCOMPLETE and contribution TECHNICAL conditional on full correctness, condition UNDISCHARGED; no necessary repair/counterexample established. T054L136 remains UNRESOLVED_FULL_SCOPE_REPAIR and NEEDS_REPAIR/INCOMPLETE. "
    "All older full targets/dispositions remain immutable, including every class VII / Kato surface / global spherical shell, Hopf and Inoue surface, Enoki and Inoue–Hirzebruch surface, curves and cycles of rational curves on non-Kähler surfaces, Kodaira classification, twisted holomorphic structures and gauge-theoretic (Donaldson/Seiberg–Witten moduli) class VII arguments, deformation of Kato data, non-Kähler complex surface and compact complex surface topology scope encountered in eligible ORIGINAL history."
)

assert new[43].startswith("Your ONE developed family is confirmed SOURCE059")
new[43] = ("Your ONE developed family is confirmed SOURCE060: THE GLOBAL SPHERICAL SHELL CONJECTURE. ONE canonical manuscript folder, ELEVEN tree blobs: Global-Spherical-Shells-on-Minimal-Surfaces-of-Class-VII (September-24; wrapper build/paper.tex of 16805 bytes, build/references.tex, one figure input build/figures/flat-chain.tex, six section inputs under build/sections named compact-data, conclusion, curves, cylinder, surfaces and weighted, README, compiled PDF). "
           "Establish from the bodies what the 16805-byte wrapper itself contains and includes, in what order the section inputs are used, which results each section states and proves, and how the figure input is used; never decide this from names. Parent infers nothing from filenames. Authenticate ALL eleven blobs. "
           "Read the wrapper, README and actual FULL headline statement, and read COMPLETELY the operative proof bodies of every section your developed operation relies on, with ALL their operative includes/required companions, strongest actual primary versions and relevant operative ORIGINAL history mechanisms BEFORE extended deductions or author drafting; disclose exactly which sections were not semantically read. "
           "Source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Validate new deductions/applicability, never audit source truth because it proves the Global Spherical Shell conjecture.")

assert new[45] == "Confirmed canonical wrappers at immutable pin:"
new[45] = "Confirmed canonical wrapper at immutable pin:"
assert new[46].startswith("preprints/Ambiently-homeomorphic-isolated-hypersurfaces-of-multiplicities-two-and-three")
new[46] = F1 + "build/paper.tex"
new[47] = "bytes16805; Git blobf79ccb59553aa128043c866d98f9b5a7ae4824b2."
assert new[48].startswith("preprints/Ambiently-homeomorphic-isolated-hypersurface-germs-in-C4") and new[49].startswith("bytes903")
del new[48:50]

assert new[49].startswith("Follow actual nested includes")
new[49] = (
    "Follow actual nested includes/ancestors and complete-tree same-family objects, including every section, figure and reference input actually included by the wrapper, whose actual contents you must establish from the bodies; no guessed wrapper and no inference of a section's content from its filename. "
    "The source already proves, per catalogue: every connected minimal compact complex surface of class VII with b₂>0 contains a global spherical shell, that is a holomorphically embedded neighborhood of the standard three-sphere in C²∖{0} whose complement is connected; this is the positive-b₂ Global Spherical Shell conjecture, so every such surface is a Kato surface. "
    "This headline, the production of curves or cycles, the compactness, cylinder, weighted or flat-chain constructions as the bodies actually perform them, the classical Kato/Dloussky/Nakamura/Enoki/Teleman inputs as the bodies actually use them, and any finite case tables are paid, not nominees. "
    "Read the actual mechanism (how curves or shells are produced, where minimality, compactness, class VII, b₂>0 and the absence of a Kähler metric are each used, how the standard three-sphere embedding and connected complement are obtained, which gauge-theoretic, pluripotential or algebraic inputs are operative, and which classical results are inputs versus outputs), the exact definitions of class VII, minimality and global spherical shell in the manuscript, and any limitation, non-uniqueness or open-case statements the source itself contains. "
    "Do NOT infer statements for b₂=0 surfaces, for non-minimal surfaces beyond blow-up transport the source states, for the number, configuration or deformation type of curves or of Kato data beyond what is stated, for moduli/Teichmüller or deformation-space structure, for higher-dimensional or non-compact analogues, for Kodaira-classification consequences beyond those stated, for uniqueness of the shell, or for strengthened effectiveness, from the proved statement. Stipulate every source operation rather than rejecting the headline by older partial results."
)

assert new[51].startswith("Develop a DISTINCT")
new[51] = new[51].replace("source germ-construction/ambient-homeomorphism/multiplicity-control mechanisms", "source class VII curve-production/shell-construction/compactness mechanisms")
new[51] = new[51].replace("routine coefficient/dimension/multiplicity substitutions, unsupported extension to non-isolated, non-reduced, abstract-homeomorphism, bi-Lipschitz, low-dimensional or deformation settings",
                          "routine Betti-number/parameter/case substitutions, unsupported extension to b₂=0, non-minimal, non-compact, higher-dimensional, moduli or deformation-family settings")
assert "curve-production/shell-construction" in new[51] and "b₂=0, non-minimal" in new[51]

text = "\n".join(new)
assert len(new) == 76
for bad in ["r158-brief", "SOURCE059", "105150", "Ambiently-homeomorphic", "47218dcf", "71919609", "bytes1014", "bytes903", "THIRTY-ONE", "TWO canonical", "BOTH manuscripts", "*arithmetic*r158* before", "Arnold", "hypersurface germ", "lean/docs/059", "fresh-arithmetic-discovery-r157/", "two-and-three", "dispatched together with this round"]:
    assert bad not in text, bad
assert text.count("Zariski") == 1 and "Zariski" in new[41]
assert "fresh-arithmetic-discovery-r159/" in text and "[106786,107733)" in text and "*arithmetic*r159*" in text and "*structural*r191*" in text
out = os.path.join(ET, "fresh-arithmetic-r159-brief.txt")
assert not os.path.exists(out)
open(out, "w", encoding="utf-8").write(text)
raw = open(out, "rb").read()
BRIEF_SHA, BRIEF_BYTES = sha(raw), len(raw)

json.dump({
    "observed_utc": NOW,
    "before_arithmetic159_root_and_brief_dispatch": True,
    "live_peers_at_composition": "Structural191 (Source315) running, not inspected or steered; sole active peer",
    "mutual_guards": {"this_brief_contains": "*structural*r191* (supplement line, inherited) and the explicit peer-namespace exclusion",
                      "peer_brief_contains": "*arithmetic*r159* (supplement line of the original Structural191 brief) and the inherited explicit exclusion of unopened arithmetic rounds"},
    "closed_round_excluded": {"Arithmetic156": "CLOSED PASS/TECHNICAL zero count; namespace excluded from broad selection; no bodies admitted"},
    "no_live_body_status_activity_or_findings_read": True,
    "completed_inputs_read_by_parent_before_brief": [
        "discovery-arithmetic-r158-parent/assessment.md (parent-authored)",
        "fresh-arithmetic-discovery-r158/packet/FINAL.md, REPORT.md, notes/00-03, notes/calculation-values.json, packet/private/READING-ISOLATION.md (at the r158 intake)",
    ],
    "limits": "Initial prompt chronology, not OS/perfect isolation.",
    "new_root_created_after_initial_guards_and_before_dispatch": True,
    "new_brief": {"path": "expanded-target-2026-10-17/fresh-arithmetic-r159-brief.txt", "sha256": BRIEF_SHA, "bytes": BRIEF_BYTES},
    "prospective_guard_supplement_in_brief": "carried: *arithmetic*r160*..r162*, *structural*r195*..r197*, *analytic*r187*..r189*; plus the no-r wildcard-twin instruction",
    "completed_exceptions_granted": "r158 parent assessment, packet FINAL, notes/01-03 and packet/private/READING-ISOLATION.md; r157 exceptions withdrawn (unrelated semialgebraic-domain family)",
    "source060_preparation": {
        "one_family": True,
        "catalogue_extent": list(EXT),
        "catalogue_sha256": BODY_SHA,
        "next_header_located_by_one_bounded_4000_byte_seek": True,
        "no_061_header_in_window": True,
        "incidental_catalogue_display": "titles/abstracts of 062-064 displayed in the bounded window as navigation only",
        "title_only_navigation_range": [43, 62],
        "canonical_objects": 11,
        "canonical_folders": 1,
        "tree_entries": [14],
        "lean_docs_link": False,
        "parent_read_source_proofs": False,
    },
}, open(os.path.join(HERE, "prospective-isolation-arithmetic159.json"), "w"), indent=1)

root = os.path.join(C, "fresh-arithmetic-discovery-r159")
os.mkdir(root)
print(json.dumps({"brief_sha256": BRIEF_SHA, "brief_bytes": BRIEF_BYTES, "root": root, "title062": title062, "body_sha256": BODY_SHA}))
