#!/usr/bin/env python3
"""Compose the Arithmetic160 brief from the Arithmetic159 brief and write the
Source062 navigation records for the Arithmetic159 parent intake."""
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


# --- Source062 catalogue body and navigation -------------------------------
EXT = (107733, 109073)
with open(os.path.join(PROJ, "sources/CONTENTS.md"), "rb") as f:
    f.seek(EXT[0])
    probe = f.read(4000)
i063 = probe.find(b"**063. ")
assert i063 == EXT[1] - EXT[0], i063
body = probe[:i063]
nxt = probe[i063:]
assert body.startswith(b"**062. Projective contact classification and the LeBrun\xe2\x80\x93Salamon conjecture.**")
assert nxt.startswith(b"**063. The generalized Mukai conjecture.**")
assert b"lean/docs" not in body
BODY_SHA = sha(body)
assert BODY_SHA == "20cbbd4a07af05e71096debe7cafc3c2467f92be956e756f699e093f7531ad1a"
with open(os.path.join(PRIV, "catalogue-062.md"), "wb") as f:
    f.write(body)
title063 = nxt[:nxt.find(b".**") + 3].decode()

nav_src = os.path.join(C, "discovery-arithmetic-r158-parent/private/title-navigation.json")
nav = json.load(open(nav_src))
assert nav["families_selected"]["060"] == "arithmetic159" and nav["next_header"]["family"] == 62
nav["numeric_range"] = [43, 63]
nav["titles"].append({"family": 62, "start": EXT[0], "title_end": None,
                      "raw": "**062. Projective contact classification and the LeBrun–Salamon conjecture.**",
                      "how": "header located at the arithmetic159 dispatch by one bounded 4000-byte seek after 106786; body [107733,109073) decoded once for arithmetic160 selection"})
nav["families_selected"]["062"] = "arithmetic160"
nav["next_header"] = {"family": 63, "start": EXT[1], "raw": title063,
                      "located_by": "one bounded 4000-byte seek after 107733; end not located",
                      "incidental_display": "the 063 title line and the earlier 062-064 abstract window were displayed to the parent as navigation only; no source theorem/proof body was read and no family other than 062 was selected"}
json.dump(nav, open(os.path.join(PRIV, "title-navigation.json"), "w"), indent=1)

# --- folder metadata --------------------------------------------------------
tree = json.load(open(os.path.join(PROJ, "sources/preprints-tree.json")))["tree"]
assert len(tree) == 13223
F1 = "preprints/Contact-Fano-manifolds-and-the-LeBrun-Salamon-conjecture-September-23-2026/"
links = [l for l in body.decode().split("](preprints/")[1:]]
assert len(links) == 1 and links[0].startswith(F1[len("preprints/"):] + "paper.pdf")
fam1 = [e for e in tree if e["path"].startswith(F1)]
b1 = [e for e in fam1 if e["type"] == "blob"]
assert (len(fam1), len(b1)) == (17, 14), (len(fam1), len(b1))
w1 = [e for e in b1 if e["path"] == F1 + "build/main.tex"][0]
assert w1["size"] == 2772 and w1["sha"] == "c8cf7fe7c816a55226c5f7a46946aecc1fd1f8b8"
assert not any(e["path"].endswith("/build/paper.tex") for e in b1)
names = sorted(e["path"][len(F1):] for e in b1)
assert names == ["README.md", "build/figures/unmarked-boundary.tex", "build/main.tex", "build/references.tex",
                 "build/sections/descent.tex", "build/sections/extension.tex", "build/sections/homogeneous.tex",
                 "build/sections/introduction.tex", "build/sections/jets.tex", "build/sections/lines.tex",
                 "build/sections/reduction.tex", "build/sections/smoothing.tex", "build/sections/twistor.tex", "paper.pdf"], names
others = [e["path"] for e in tree if "lebrun" in e["path"].lower() and not e["path"].startswith(F1.rstrip("/"))]
assert not others, others
json.dump({
    "family": 62,
    "catalogue_extent": list(EXT),
    "catalogue_sha256": BODY_SHA,
    "next_header_confirmed": "%s at %d" % (title063, EXT[1]),
    "folders": [F1.rstrip("/")],
    "blobs_per_folder": [14],
    "total_blobs": 14,
    "tree_entries": [17],
    "candidate_top_level_tex": ["build/main.tex (2772 B, blob c8cf7fe7c816a55226c5f7a46946aecc1fd1f8b8)"],
    "blob_names_only": names,
    "lean_docs_link": False,
    "parent_read_source_proofs": False,
}, open(os.path.join(PRIV, "source062-selection.json"), "w"), indent=1)

# --- brief --------------------------------------------------------------------
ET = os.path.join(C, "expanded-target-2026-10-17")
old = open(os.path.join(ET, "fresh-arithmetic-r159-brief.txt"), encoding="utf-8").read().split("\n")
assert len(old) == 76
new = list(old)
assert new[0].startswith("Arithmetic discovery r159")
new[0] = "Arithmetic discovery r160 — confirmed contact-Fano homogeneity / LeBrun–Salamon (positive quaternionic-Kähler) operative-proof discovery."
new[1] = "Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r160/."

a = new[9].index("The ORIGINAL INITIAL brief of Structural191")
b = new[9].index("Exact COMPLETED exceptions do not widen containing directories.") + len("Exact COMPLETED exceptions do not widen containing directories.")
new[9] = new[9][:a] + (
    "The ORIGINAL INITIAL brief of Structural192, dispatched before this round, contains the literal prospective guard *arithmetic*r160* before any arithmetic160 body existed, and this brief contains *structural*r192* while structural192 is live. "
    "Structural192 (Source316, its author root and parent records) is the only current active peer: exclude the ENTIRE *structural*r192* namespace and every body/parent/brief/copy/derivative/status/activity alias. "
    "Arithmetic156 is COMPLETED and CLOSED whole-scope PASS/TECHNICAL with ZERO count (its author root, both review roots and parent records are no longer live): exclude the ENTIRE *arithmetic*r156* namespace from broad selection; no bodies admitted. "
    "Arithmetic159, Structural191, Arithmetic158, Structural190, Structural189, Arithmetic157, Arithmetic155, Structural188, Structural187, Arithmetic154, Arithmetic153, Structural186, Arithmetic152, Arithmetic151 and Arithmetic150 are COMPLETED PREFREEZE/no nominee and parent-archived; exclude every arithmetic159, structural191, arithmetic158, structural190, structural189, arithmetic157, arithmetic155, structural188, structural187, arithmetic154, arithmetic153, structural186, arithmetic152, arithmetic151 and arithmetic150 namespace from broad selection; only the exact COMPLETED exceptions below are direct reads. "
    "Also exclude every full-path alias of a completed or live round that lacks the literal r (for example arithmetic151-stopped.json style status aliases, arithmetic15N*, arithmetic16N*, structural19N*, analytic18N*) by installing the no-r wildcard twins of every listed guard before traversal. "
    "Own arithmetic160 namespace remains excluded from broad authored-history scans; own files usable. No peer body/status/activity/summary/finding may be inspected, inferred or used as premise. Do not inspect or steer peers to certify supplied isolation. This is prompt chronology, not OS/perfect isolation. Exact COMPLETED exceptions do not widen containing directories."
) + new[9][b:]

assert new[39].startswith("Catalogue access for THIS round")
new[39] = ("Catalogue access for THIS round, if needed at all: ONLY direct binary seek/read sources/CONTENTS.md[107733,109073), confirmed exact Source062 body. "
           "Parent reused numeric-header TITLE-ONLY43–62 (no 061 header exists; numeric headers are not contiguous), located the 063 header by one bounded 4000-byte seek after 107733 and selected ONLY this family; the bounded windows displayed catalogue title/abstract text of families 062–064 to the parent as navigation only; parent has NOT read source theorem/proof bodies. The body links no Lean documentation page. "
           "No child catalogue scan, heading locator, read_text/readlines/whole read_bytes/decode or extra family. Full-tree metadata predicates use casefolded FULL paths. Selector failure is disclosed, never authorization for a wider span.")

assert new[41].startswith("Read these exact COMPLETED originals")
new[41] = (
    "Read these exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/: discovery-arithmetic-r159-parent/assessment.md; fresh-arithmetic-discovery-r159/packet/FINAL.md; fresh-arithmetic-discovery-r159/packet/notes/01-primary-payment.md; fresh-arithmetic-discovery-r159/packet/notes/02-triangular-and-spectral-reduction.md; fresh-arithmetic-discovery-r159/packet/notes/03-relative-operation.md; fresh-arithmetic-discovery-r159/packet/private/READING-ISOLATION.md. These completed inputs admit no containing namespace or status/activity access. "
    "Arithmetic159 remains PREFREEZE/no nominee: on Source060 (the Global Spherical Shell conjecture) it pays the 0/1 integral identification of the source compact class, the triangular identification of the source zero divisor as a finite sum of Dloussky–Teleman fundamental divisors with end orientation, exact rational phase generating functions and the fixed-fiber weighted-mass threshold β>log ρ from the periodic recurrence, and the full family reduction to b compact reference curves with the finite spectral constant paid; the uniform weighted-area estimate (G) for the actual marked DT reference curves at every supercritical exponent through changes of curve configuration including the Enoki branch remains unpaid, and its class VII scope is not this family. "
    "Arithmetic158 (vanishing of the determinant class χ in the full quotient for the once-squared Zariski-multiplicity lattices, or complementary marked splittings, unpaid), Structural191 (full-scope construction of finite-support real filling columns with simultaneous power-decay residual and power-growth norm bounds for every finite aspherical integral PD4 complex, or an equally strong closed geometric substitute, unpaid), Structural190 (structural finite-precision elimination or global chain exchange with an a priori stabilization bound for cyclic lengths of finite p-group products unpaid), Structural189 (source-specific effectively represented all-orders chain contraction in the deformation-adic filtration unpaid), Arithmetic157 (good-point/moving-center multiple-scale normalization anchor for finite-volume semialgebraic domains unpaid), Arithmetic155 (geometric control of the low places spendable by negative small diagrams in generalized-canonical Kähler fourfold flip sequences unpaid), Structural188 (collapse-preserving lift c_S θ̃=θ c_j for every freely adjoined coherator operation unpaid), Structural187 (effective sampling constants/coordinate transfer or all-strata orbit-ideal lifting unpaid), Arithmetic154 (continuation of the quintic stability family through s=0 to the Gepner point unpaid), Arithmetic153 (geometric integrally marked gluing transport unpaid), Arithmetic152 (exact marked cancellation at the original exponent for b≥302 unpaid), Arithmetic151 (global holomorphic correction outside Calabi–Yau-base cases unpaid), Arithmetic150, Structural186 (uniform mixed overlap/attachment control across distinct extensions unpaid), Structural185, Arithmetic149/148, Structural184 and Analytic177 remain PREFREEZE/no nominee at their exact gaps. No retry/general impossibility. "
    "Arithmetic156 (Source057 root-stack fundamental-group isomorphism for the four-factor diagonal-quadric eightfold), Arithmetic147, S183N, S182P, Analytic161/T337A161 and T366A166 are whole-scope PASS/TECHNICAL, correctness conditions DISCHARGED, ZERO count; no bodies admitted or desired-grade retries. S176A remains correctness INCOMPLETE and contribution TECHNICAL conditional on full correctness, condition UNDISCHARGED; no necessary repair/counterexample established. T054L136 remains UNRESOLVED_FULL_SCOPE_REPAIR and NEEDS_REPAIR/INCOMPLETE. "
    "All older full targets/dispositions remain immutable, including every contact Fano manifold, adjoint variety, projective contact manifold and P(T*Z) classification, quaternionic-Kähler and Wolf space, twistor space and twistor correspondence, LeBrun–Salamon, Kebekus–Peternell–Sommese–Wiśniewski, Demailly or Beauville contact-line argument, rational curves/lines on Fano manifolds, jet/extension/smoothing/descent of contact structures, homogeneous Fano manifolds and Kobayashi–Ochiai, Mori or Mukai-type Fano classification scope encountered in eligible ORIGINAL history."
)

assert new[43].startswith("Your ONE developed family is confirmed SOURCE060")
new[43] = ("Your ONE developed family is confirmed SOURCE062: PROJECTIVE CONTACT CLASSIFICATION AND THE LEBRUN–SALAMON CONJECTURE. ONE canonical manuscript folder, FOURTEEN tree blobs: Contact-Fano-manifolds-and-the-LeBrun-Salamon-conjecture (September-23; wrapper build/main.tex of 2772 bytes, build/references.tex, one figure input build/figures/unmarked-boundary.tex, nine section inputs under build/sections named descent, extension, homogeneous, introduction, jets, lines, reduction, smoothing and twistor, README, compiled PDF). "
           "Establish from the bodies what the 2772-byte wrapper itself contains and includes, in what order the section inputs are used, which results each section states and proves, and how the figure input is used; never decide this from names. Parent infers nothing from filenames. Authenticate ALL fourteen blobs. "
           "Read the wrapper, README and actual FULL headline statements, and read COMPLETELY the operative proof bodies of every section your developed operation relies on, with ALL their operative includes/required companions, strongest actual primary versions and relevant operative ORIGINAL history mechanisms BEFORE extended deductions or author drafting; disclose exactly which sections were not semantically read. "
           "Source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Validate new deductions/applicability, never audit source truth because it proves contact-Fano homogeneity and the LeBrun–Salamon conjecture.")

assert new[45] == "Confirmed canonical wrapper at immutable pin:"
assert new[46].startswith("preprints/Global-Spherical-Shells")
new[46] = F1 + "build/main.tex"
assert new[47].startswith("bytes16805")
new[47] = "bytes2772; Git blobc8cf7fe7c816a55226c5f7a46946aecc1fd1f8b8."

assert new[49].startswith("Follow actual nested includes")
new[49] = (
    "Follow actual nested includes/ancestors and complete-tree same-family objects, including every section, figure and reference input actually included by the wrapper, whose actual contents you must establish from the bodies; no guessed wrapper and no inference of a section's content from its filename. "
    "The source already proves, per catalogue: every smooth connected complex projective contact Fano manifold of complex dimension at least three, with its given contact distribution, is contact-isomorphic to the adjoint variety of a simple complex Lie algebra (contact-Fano homogeneity); smooth connected complex projective contact manifolds of complex dimension at least three are classified, those with b₂=1 being adjoint varieties with their canonical contact structures and those with b₂≥2 having underlying manifold P(T*Z) for a smooth projective variety Z; and consequently every closed connected smooth positive quaternionic-Kähler manifold of real dimension 4m≥8 is homothetic to a compact symmetric Wolf space (the LeBrun–Salamon conjecture). "
    "These headlines, the twistor correspondence, the reduction, line, jet, extension, smoothing, descent and homogeneity arguments as the bodies actually perform them, the classical LeBrun–Salamon, Salamon, Kebekus–Peternell–Sommese–Wiśniewski, Demailly, Beauville, Kobayashi–Ochiai or Mori inputs as the bodies actually use them, and any finite case tables are paid, not nominees. "
    "Read the actual mechanism (how the twistor space of a positive quaternionic-Kähler manifold enters, how projectivity, the Fano condition, b₂ and dimension at least three are each used, how lines or rational curves and their jets are controlled, what is extended and smoothed and how descent to the adjoint variety or to P(T*Z) is obtained, which algebraic, differential-geometric or representation-theoretic inputs are operative, and which classical results are inputs versus outputs), the exact definitions of contact manifold, contact Fano manifold, adjoint variety and positive quaternionic-Kähler manifold in the manuscript, and any limitation or open-case statements the source itself contains. "
    "Do NOT infer statements for real dimension four (m=1), for non-positive, Ricci-flat, noncompact or orbifold quaternionic-Kähler manifolds, for non-projective Kähler, singular or non-Fano contact manifolds beyond the stated b₂≥2 classification, for contact structures in dimension one or two, for moduli or deformation-space structure, for uniqueness or rigidity of contact structures beyond what is stated, or for strengthened effectiveness, from the proved statements. Stipulate every source operation rather than rejecting the headlines by older partial results."
)

assert new[51].startswith("Develop a DISTINCT")
new[51] = new[51].replace("source class VII curve-production/shell-construction/compactness mechanisms", "source twistor/line/jet/extension/smoothing/descent mechanisms")
new[51] = new[51].replace("routine Betti-number/parameter/case substitutions, unsupported extension to b₂=0, non-minimal, non-compact, higher-dimensional, moduli or deformation-family settings",
                          "routine dimension/rank/case substitutions, unsupported extension to real dimension four, non-positive, noncompact, orbifold, non-projective, singular or moduli settings")
assert "twistor/line/jet" in new[51] and "real dimension four" in new[51]

text = "\n".join(new)
assert len(new) == 76
for bad in ["r159-brief", "SOURCE060", "106786", "Global-Spherical-Shells", "f79ccb59", "bytes16805", "ELEVEN", "flat-chain", "compact-data", "Structural191 (Source315, its author root", "*arithmetic*r159* before", "fresh-arithmetic-discovery-r158/", "discovery-arithmetic-r158-parent", "Kato/Dloussky/Nakamura", "class VII curve-production", "b₂=0, non-minimal"]:
    assert bad not in text, bad
assert text.count("Zariski") == 1 and "Zariski" in new[41] and text.count("Global Spherical Shell") == 1
assert "fresh-arithmetic-discovery-r160/" in text and "[107733,109073)" in text and "*arithmetic*r160*" in text and "*structural*r192*" in text
out = os.path.join(ET, "fresh-arithmetic-r160-brief.txt")
assert not os.path.exists(out)
open(out, "w", encoding="utf-8").write(text)
raw = open(out, "rb").read()
BRIEF_SHA, BRIEF_BYTES = sha(raw), len(raw)

json.dump({
    "observed_utc": NOW,
    "before_arithmetic160_root_and_brief_dispatch": True,
    "live_peers_at_composition": "Structural192 (Source316) running, not inspected or steered; sole active peer",
    "mutual_guards": {"this_brief_contains": "*structural*r192* (supplement line, inherited) and the explicit peer-namespace exclusion",
                      "peer_brief_contains": "*arithmetic*r160* (supplement line of the original Structural192 brief) and the inherited explicit exclusion of unopened arithmetic rounds"},
    "closed_round_excluded": {"Arithmetic156": "CLOSED PASS/TECHNICAL zero count; namespace excluded from broad selection; no bodies admitted"},
    "no_live_body_status_activity_or_findings_read": True,
    "completed_inputs_read_by_parent_before_brief": [
        "discovery-arithmetic-r159-parent/assessment.md (parent-authored)",
        "fresh-arithmetic-discovery-r159/packet/FINAL.md, REPORT.md, notes/00-03 (00-01 partly display-truncated), notes/recurrence_calculation.py, notes/calculation-values.json, packet/private/READING-ISOLATION.md (at the r159 intake)",
    ],
    "limits": "Initial prompt chronology, not OS/perfect isolation.",
    "new_root_created_after_initial_guards_and_before_dispatch": True,
    "new_brief": {"path": "expanded-target-2026-10-17/fresh-arithmetic-r160-brief.txt", "sha256": BRIEF_SHA, "bytes": BRIEF_BYTES},
    "prospective_guard_supplement_in_brief": "carried: *arithmetic*r160*..r162*, *structural*r195*..r197*, *analytic*r187*..r189*; plus the no-r wildcard-twin instruction",
    "completed_exceptions_granted": "r159 parent assessment, packet FINAL, notes/01-03 and packet/private/READING-ISOLATION.md; r158 exceptions withdrawn (unrelated Zariski-multiplicity lattice family, listed with its unpaid operation)",
    "source062_preparation": {
        "one_family": True,
        "catalogue_extent": list(EXT),
        "catalogue_sha256": BODY_SHA,
        "next_header_located_by_one_bounded_4000_byte_seek": True,
        "no_061_header": True,
        "incidental_catalogue_display": "titles/abstracts of 062-064 displayed in earlier bounded window and the 063 title line now, as navigation only",
        "title_only_navigation_range": [43, 63],
        "canonical_objects": 14,
        "canonical_folders": 1,
        "tree_entries": [17],
        "wrapper": "build/main.tex (no build/paper.tex in this folder)",
        "lean_docs_link": False,
        "parent_read_source_proofs": False,
    },
}, open(os.path.join(HERE, "prospective-isolation-arithmetic160.json"), "w"), indent=1)

root = os.path.join(C, "fresh-arithmetic-discovery-r160")
os.mkdir(root)
print(json.dumps({"brief_sha256": BRIEF_SHA, "brief_bytes": BRIEF_BYTES, "root": root, "title063": title063, "body_sha256": BODY_SHA}))
