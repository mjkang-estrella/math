#!/usr/bin/env python3
"""Compose the Structural191 brief from the Structural190 brief and write the
Source315 navigation records for the Structural190 parent intake."""
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


# --- Source315 catalogue body and navigation -------------------------------
EXT = (537826, 538801)
with open(os.path.join(PROJ, "sources/CONTENTS.md"), "rb") as f:
    f.seek(EXT[0])
    body = f.read(EXT[1] - EXT[0])
    f.seek(EXT[1])
    nxt = f.read(4000)
assert body.startswith(b"**315. The four-dimensional Singer conjecture.**")
assert nxt.startswith(b"**316. Curtis\xe2\x80\x99s conjecture.**")
i317 = nxt.find(b"**317. ")
assert i317 >= 0
assert b"lean/docs" not in body
BODY_SHA = sha(body)
with open(os.path.join(PRIV, "catalogue-315.md"), "wb") as f:
    f.write(body)

nav_src = os.path.join(C, "discovery-structural-r189-parent/private/title-navigation.json")
nav = json.load(open(nav_src))
assert nav["families_selected"][-1] == {"family": 314, "round": "structural190"}
assert nav["next_header"]["family"] == 315 and nav["next_header"]["start"] == EXT[0]
title317 = nxt[i317:nxt.find(b".**", i317) + 3].decode()
nav["numeric_range"] = [300, 317]
nav["titles"].append({"family": 317, "start": EXT[1] + i317,
                      "title_end": EXT[1] + i317 + len(title317.encode()),
                      "raw": title317})
nav["families_selected"].append({"family": 315, "round": "structural191"})
nav["next_header"] = {"family": 316, "start": EXT[1],
                      "located_by": "316 header located earlier in the bounded window after 536770; body [537826,538801) decoded once for structural191 selection; 317 header located by one bounded 4000-byte seek after 538801"}
json.dump(nav, open(os.path.join(PRIV, "title-navigation.json"), "w"), indent=1)

# --- folder metadata --------------------------------------------------------
tree = json.load(open(os.path.join(PROJ, "sources/preprints-tree.json")))["tree"]
assert len(tree) == 13223
PRE = "preprints/The-Singer-conjecture-in-dimension-four-September-25-2026/"
assert body.decode().count("](preprints/") == 1 and PRE[len("preprints/"):] in body.decode()
fam = [e for e in tree if e["path"].startswith(PRE)]
blobs = [e for e in fam if e["type"] == "blob"]
assert len(fam) == 17 and len(blobs) == 16, (len(fam), len(blobs))
wrap = [e for e in blobs if e["path"] == PRE + "build/paper.tex"][0]
assert wrap["size"] == 1698 and wrap["sha"] == "58c43c1b0867d5b1407147d9363765c528be31a8"
texs = sorted(e["path"][len(PRE):] for e in blobs if e["path"].endswith(".tex"))
assert len(texs) == 13 and "build/paper.tex" in texs
others = [e["path"] for e in tree if "singer-conjecture" in e["path"].lower() and not e["path"].startswith(PRE.rstrip("/"))]
assert not others, others
json.dump({
    "family": 315,
    "catalogue_extent": list(EXT),
    "catalogue_sha256": BODY_SHA,
    "next_header_confirmed": "**316. Curtis's conjecture.** at 538801 (located earlier); 317 header at %d" % (EXT[1] + i317),
    "folders": [PRE.rstrip("/")],
    "blobs_per_folder": [16],
    "total_blobs": 16,
    "tree_entries": 17,
    "candidate_top_level_tex": ["build/paper.tex (1698 B, blob 58c43c1b0867d5b1407147d9363765c528be31a8)"],
    "tex_objects": texs,
    "lean_docs_link": False,
    "parent_read_source_proofs": False,
}, open(os.path.join(PRIV, "source315-selection.json"), "w"), indent=1)

# --- brief --------------------------------------------------------------------
ET = os.path.join(C, "expanded-target-2026-10-17")
old = open(os.path.join(ET, "fresh-structural-r190-brief.txt"), encoding="utf-8").read().split("\n")
assert len(old) == 76
new = list(old)
assert new[0].startswith("Structural discovery r190")
new[0] = "Structural discovery r191 — confirmed four-dimensional Singer conjecture operative-proof discovery."
new[1] = "Write ONLY frontier/campaigns/2026-10-14/fresh-structural-discovery-r191/."

a = new[9].index("The ORIGINAL INITIAL briefs")
b = new[9].index("Exact COMPLETED exceptions do not widen containing directories.") + len("Exact COMPLETED exceptions do not widen containing directories.")
new[9] = new[9][:a] + (
    "The ORIGINAL INITIAL brief of Arithmetic158, dispatched together with this round, contains the literal prospective guard *structural*r191* before any structural191 body existed, and this brief contains *arithmetic*r158* before any arithmetic158 body exists. "
    "Arithmetic158 (Source059, its author root and parent records) is the only current active peer: exclude the ENTIRE *arithmetic*r158* namespace and every body/parent/brief/copy/derivative/status/activity alias. "
    "Arithmetic156 is COMPLETED and CLOSED whole-scope PASS/TECHNICAL with ZERO count (its author root, both review roots and parent records are no longer live): exclude the ENTIRE *arithmetic*r156* namespace from broad selection; no bodies admitted. "
    "Structural190, Structural189, Arithmetic157, Arithmetic155, Structural188, Structural187, Arithmetic154, Arithmetic153, Structural186, Arithmetic152, Arithmetic151 and Arithmetic150 are COMPLETED PREFREEZE/no nominee and parent-archived; exclude every structural190, structural189, arithmetic157, arithmetic155, structural188, structural187, arithmetic154, arithmetic153, structural186, arithmetic152, arithmetic151 and arithmetic150 namespace from broad selection; only the exact COMPLETED exceptions below are direct reads. "
    "Also exclude every full-path alias of a completed or live round that lacks the literal r (for example arithmetic151-stopped.json style status aliases, arithmetic15N*, structural19N*, analytic18N*) by installing the no-r wildcard twins of every listed guard before traversal; the completed Structural190 round disclosed that the literal-r wildcards alone admitted two such aliases lexically. "
    "Own structural191 namespace remains excluded from broad authored-history scans; own files usable. No peer body/status/activity/summary/finding may be inspected, inferred or used as premise. Do not inspect or steer peers to certify supplied isolation. This is prompt chronology, not OS/perfect isolation. Exact COMPLETED exceptions do not widen containing directories."
) + new[9][b:]

assert new[39].startswith("Catalogue access for THIS round")
new[39] = ("Catalogue access for THIS round, if needed at all: ONLY direct binary seek/read sources/CONTENTS.md[537826,538801), confirmed exact Source315 body. "
           "Parent reused numeric-header TITLE-ONLY300–317, located the 317 header by one bounded 4000-byte seek after 538801 and selected ONLY this family; parent has NOT read source theorem/proof bodies. The body links no Lean documentation page. "
           "No child catalogue scan, heading locator, read_text/readlines/whole read_bytes/decode or extra family. Full-tree metadata predicates use casefolded FULL paths. Selector failure is disclosed, never authorization for a wider span.")

assert new[41].startswith("Read these exact COMPLETED originals")
new[41] = (
    "Read these exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/: discovery-structural-r190-parent/assessment.md; fresh-structural-discovery-r190/FINAL.md; fresh-structural-discovery-r190/INTERFACES.md; fresh-structural-discovery-r190/DERIVATIONS.md; fresh-structural-discovery-r190/COMPARISON.md; fresh-structural-discovery-r190/private/READING-LIMITS.md. These completed inputs admit no containing namespace or status/activity access; Structural189 and Structural187 (K(n)-local/chromatic families) are unrelated to this family and admit no exceptions. "
    "Structural190 remains PREFREEZE/no nominee: on Source314 (cyclic length and chromatic fixed-point loss) it pays the relative compactness reuse of the source's product-series lemma giving eventual equality of ell(P x (Z/p^r)^k, H x 0) with ell(P,H)+k, a terminating finite equality search with honest stopping condition, an exact subgroup model with normality and cyclic-edge criteria, a diagonal control showing local rank-charging loses the extension coupling, and a modular delay family with least stabilization precision exactly m-1 so that no bound in (p,k,ell(P,H)) alone exists; a structural finite-precision elimination or global chain exchange yielding an a priori stabilization bound from finite structural data for every pair and k remains unpaid. "
    "Structural189 (source-specific effectively represented all-orders chain contraction in the deformation-adic filtration unpaid), Structural188 (collapse-preserving lift c_S θ̃=θ c_j for every freely adjoined coherator operation after globular-sum gluing unpaid), Structural187 (effective sampling constants/coordinate transfer or all-strata orbit-ideal lifting unpaid), Arithmetic157 (good-point/moving-center multiple-scale normalization supplying a compact-normalized interior anchor for two-sided scaling closure of bounded-symmetry finite-volume domains unpaid), Arithmetic155 (geometric control of the low places spendable by negative small diagrams in generalized-canonical Kähler fourfold flip sequences unpaid), Arithmetic154 (continuation of the quintic stability family through s=0 to the Gepner point unpaid), Arithmetic153 (geometric integrally marked gluing transport unpaid), Arithmetic152 (exact marked cancellation at the original exponent for b≥302 unpaid), Arithmetic151 (global holomorphic correction outside Calabi–Yau-base cases unpaid), Arithmetic150, Structural186 (uniform mixed overlap/attachment control across distinct extensions unpaid), Structural185, Arithmetic149/148, Structural184 and Analytic177 remain PREFREEZE/no nominee at their exact gaps. No retry/general impossibility. "
    "Arithmetic156 (Source057 root-stack fundamental-group isomorphism for the four-factor diagonal-quadric eightfold), Arithmetic147, S183N, S182P, Analytic161/T337A161 and T366A166 are whole-scope PASS/TECHNICAL, correctness conditions DISCHARGED, ZERO count; no bodies admitted or desired-grade retries. S176A remains correctness INCOMPLETE and contribution TECHNICAL conditional on full correctness, condition UNDISCHARGED; no necessary repair/counterexample established. T054L136 remains UNRESOLVED_FULL_SCOPE_REPAIR and NEEDS_REPAIR/INCOMPLETE. "
    "All older full targets/dispositions remain immutable, including every L²-Betti number/L²-invariant, Singer/Hopf/Atiyah conjecture, aspherical manifold/Poincaré complex, group von Neumann algebra/Lück approximation, four-manifold topology/surgery, geometric group theory (boundaries, pretrees, cut points, splittings, JSJ), hyperbolic and relatively hyperbolic group, Gromov boundary dynamics and compactification scope encountered in eligible ORIGINAL history."
)

assert new[43].startswith("Your ONE developed family is confirmed SOURCE314")
new[43] = ("Your ONE developed family is confirmed SOURCE315: THE FOUR-DIMENSIONAL SINGER CONJECTURE. ONE canonical manuscript folder, SIXTEEN tree blobs: wrapper build/paper.tex of 1698 bytes, twelve further .tex inputs directly under build/ (annular-chains, annuli, blocks, boundary-topology, compactification, conclusion, consequences, dynamics, foundations, introduction, path-pushing, pretree), references.bib, README and compiled PDF (one further tree entry is the build directory). "
           "Parent infers nothing from filenames; establish from the wrapper which inputs are actually included and in what order. Authenticate ALL sixteen blobs; read actual FULL statements and ALL operative includes/required companions, strongest actual primary versions and relevant operative ORIGINAL history mechanisms BEFORE extended deductions or author drafting; disclose exactly which sections were not semantically read. "
           "Source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Validate new deductions/applicability, never audit source truth because it resolves a previously open conjecture.")

assert new[46].startswith("preprints/Cyclic-Length")
new[46] = PRE + "build/paper.tex"
new[47] = "bytes1698; Git blob58c43c1b0867d5b1407147d9363765c528be31a8."

assert new[49].startswith("Follow actual nested includes")
new[49] = (
    "Follow actual nested includes/ancestors and complete-tree same-family objects, including every .tex input and bibliography actually included by the wrapper; no guessed wrapper and no inference of a section's content from its filename. "
    "The source already proves, per catalogue: the L²-Betti numbers of the universal cover of every closed connected aspherical topological four-manifold vanish outside degree two; more generally the same vanishing holds for every finite connected aspherical integral Poincaré complex of formal dimension four, including nonorientable ones, proving the four-dimensional Singer conjecture in this wider class. "
    "These headlines, the reductions as actually invoked, the classical L²-invariant, Poincaré-duality, group-boundary/compactification, pretree/cut-point, path-pushing and dynamical inputs as the bodies actually use them, and any compiled case analyses are paid, not nominees. "
    "Read the actual mechanism (how the vanishing in degrees 0, 1, 3 and 4 is obtained and which degrees need which argument, where asphericity, finiteness, formal dimension four, the integral Poincaré-duality hypothesis and orientability or its absence are each used, which group-theoretic dichotomies, splittings, boundaries, compactifications or dynamical arguments the bodies actually construct, how the first L²-Betti number is controlled and how duality transfers the conclusion, and which classical results are inputs versus outputs), the exact definitions and conventions for L²-Betti numbers, aspherical Poincaré complexes and formal dimension in this manuscript, and any counterexample, limitation or open-case statements the source itself contains. "
    "Do NOT infer statements for other dimensions, for non-aspherical, non-finite or non-Poincaré complexes, for the Hopf/Euler-characteristic sign conjecture, the Atiyah conjecture, Novikov–Shubin invariants, L²-torsion or the Lück approximation beyond what is stated, for the second L²-Betti number's value or vanishing, for smooth or geometric structures, for infinite-index subgroups, group-theoretic consequences or specific group classes beyond what the bodies prove, or for finer structure than stated, from the proved statements. Stipulate every source operation rather than rejecting the headline by older partial results."
)

assert new[51].startswith("Develop a DISTINCT")
new[51] = new[51].replace("source fixed-point-loss/subnormal-chain/sharpness mechanisms", "source L²-vanishing/duality/boundary-dynamics mechanisms")
new[51] = new[51].replace("routine prime, height, subgroup or finite-spectrum substitutions, unsupported extension to non-p-groups, compact Lie groups or other fixed-point functors, unsupported explicit witness, rank or growth bounds or uniformity claims",
                          "routine dimension, coefficient or group-class substitutions, unsupported extension to higher dimensions, non-aspherical or non-finite complexes, Hopf/Atiyah/L²-torsion consequences or other L²-invariants, unsupported explicit bounds or uniformity claims")
assert "L²-vanishing/duality/boundary-dynamics" in new[51] and "non-aspherical or non-finite complexes" in new[51]

text = "\n".join(new)
for bad in ["r190-brief", "SOURCE314", "536770", "537826)", "Cyclic-Length-and-Chromatic", "b4df60ac", "of 771 bytes", "bytes771", "THIRTEEN", "CYCLIC LENGTH AND CHROMATIC", "Kuhn–Lloyd framework", "*structural*r190* before", "live Arithmetic156 review rounds", "fresh-structural-discovery-r189/", "fresh-structural-discovery-r187/", "discovery-structural-r187-parent"]:
    assert bad not in text, bad
assert "fresh-structural-discovery-r191/" in text and "[537826,538801)" in text and "*arithmetic*r158*" in text and "*structural*r191*" in text
out = os.path.join(ET, "fresh-structural-r191-brief.txt")
assert not os.path.exists(out)
open(out, "w", encoding="utf-8").write(text)
raw = open(out, "rb").read()
BRIEF_SHA, BRIEF_BYTES = sha(raw), len(raw)

json.dump({
    "observed_utc": NOW,
    "before_structural191_root_and_brief_dispatch": True,
    "live_peers_at_composition": "none running; Arithmetic158 (Source059) is composed and dispatched in the same parent step and is the sole active peer",
    "mutual_guards": {"this_brief_contains": "*arithmetic*r158* (supplement line, inherited) and the explicit peer-namespace exclusion",
                      "peer_brief_contains": "*structural*r191* (supplement line, inherited) and the explicit peer-namespace exclusion"},
    "closed_round_excluded": {"Arithmetic156": "CLOSED PASS/TECHNICAL zero count; namespace excluded from broad selection; no bodies admitted"},
    "no_live_body_status_activity_or_findings_read": True,
    "completed_inputs_read_by_parent_before_brief": [
        "fresh-structural-discovery-r190/FINAL.md",
        "fresh-structural-discovery-r190/REPORT.md",
        "fresh-structural-discovery-r190/DERIVATIONS.md",
        "fresh-structural-discovery-r190/COMPARISON.md",
        "fresh-structural-discovery-r190/ANCHORS.json",
        "fresh-structural-discovery-r190/verify_packet.py",
        "fresh-structural-discovery-r190/private/modular_calculation.py",
        "fresh-structural-discovery-r190/INTERFACES.md (opening)",
        "fresh-structural-discovery-r190/private/READING-LIMITS.md (guard-failure disclosure and opening)",
    ],
    "limits": "Initial prompt chronology, not OS/perfect isolation.",
    "new_root_created_after_initial_guards_and_before_dispatch": True,
    "new_brief": {"path": "expanded-target-2026-10-17/fresh-structural-r191-brief.txt", "sha256": BRIEF_SHA, "bytes": BRIEF_BYTES},
    "prospective_guard_supplement_in_brief": "carried: *arithmetic*r160*..r162*, *structural*r195*..r197*, *analytic*r187*..r189*; plus the no-r wildcard-twin instruction closing the alias admission disclosed by the completed Structural190 round",
    "completed_exceptions_granted": "r190 FINAL/INTERFACES/DERIVATIONS/COMPARISON/READING-LIMITS and parent assessment; r189 and r187 exceptions withdrawn (unrelated K(n)-local/chromatic families)",
    "source315_preparation": {
        "one_family": True,
        "catalogue_extent": list(EXT),
        "catalogue_sha256": BODY_SHA,
        "next_header_located_by_one_bounded_4000_byte_seek": True,
        "title_only_navigation_range": [300, 317],
        "canonical_objects": 16,
        "canonical_folders": 1,
        "tree_entries": 17,
        "lean_docs_link": False,
        "parent_read_source_proofs": False,
    },
}, open(os.path.join(HERE, "prospective-isolation.json"), "w"), indent=1)

root = os.path.join(C, "fresh-structural-discovery-r191")
os.mkdir(root)
print(json.dumps({"brief_sha256": BRIEF_SHA, "brief_bytes": BRIEF_BYTES, "root": root, "title317": title317, "body_sha256": BODY_SHA}))
