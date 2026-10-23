#!/usr/bin/env python3
"""Prepare one isolated graph-metric discovery brief; does not dispatch."""
from pathlib import Path
import hashlib
import json
import re

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
D = Path(__file__).resolve().parent
old_raw = (B / 'expanded-target-2026-10-17/fresh-arithmetic-r162x-brief.txt').read_bytes()
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = old_raw.split(marker, 1)[1]
assert len(standing) == 5570
old = old_raw.decode()
prefix = old[:old.index('Catalogue access, if needed:')]
prefix = prefix.replace('r162x', 'r162y').replace('Source088', 'Source089').replace('projection-body operative-proof discovery', 'graph-metric operative-proof discovery')
isolation = old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
preserved = '''Arithmetic162x is CLOSED PREFREEZE/no nominee, with no frozen theorem or gate. Preserve its FULL diagnostic: ONE numerical c>0 independent of n for EVERY n>=4 and EVERY full-dimensional compact convex body K, including nonsymmetric/nonsmooth bodies, normalized UNPOLARIZED projection-volume deficit >=c times squared relative symmetric-difference asymmetry to a SAME-VOLUME translated ellipsoid. Use the deficit itself, NOT its nth root. Source scalar coercivity, SAME affine position and joint angular slack, dimension-uniform radial-volume conversion for the variational witness, the full rough O(n^5) squared-asymmetry comparison and smooth harmonic second variation are PAID. The full dimension-uniform transfer to the ORIGINAL arbitrary K retaining the SAME projection pairing, first-variation deficit and angular slack remains unpaid. A Cn same-witness transfer is sufficient, not asserted necessary to every proof. General-Wulff n-losses, separate affine positions, radial closeness without compatible gradients and curvature-local iteration do not close it. No restricted retry, renamed diagnostic, weaker substitute or method-to-counterexample inference. The scope violation of whole-journal raw-byte hashing without broader decoding and incomplete transitive primary reading remain disclosed. Do not repeat that overbroad byte access. Prior RP4/R041 reverse-projection and every earlier scope stay immutable.

'''
direct = [
    'discovery-arithmetic-r162x-parent/assessment.md',
    'fresh-arithmetic-discovery-r162x/FINAL.md',
    'fresh-arithmetic-discovery-r162x/packet/private/prefreeze-mathematics.md',
    'fresh-arithmetic-discovery-r162x/packet/private/primary-understanding.md',
    'fresh-arithmetic-discovery-r162x/packet/private/READING-LIMITS.md',
]
inputs = []
for name in direct:
    path = B / name
    raw = path.read_bytes()
    inputs.append({'path': str(path.relative_to(P)), 'bytes': len(raw),
                   'mode': path.stat().st_mode, 'sha256': hashlib.sha256(raw).hexdigest()})
nav = json.loads((D / 'private/canonical-navigation.json').read_text())
catalogue = '''Catalogue access, if needed: ONLY binary seek/read sources/CONTENTS.md[147957,149459), EXACT Source089 body. Parent decoded only the first TWO numeric-bold title strings from ONE bounded 14000-byte window and then ONLY089 body. No child title locator, catalogue screen, extra family, ancestor hunt or whole-catalogue opening/decoding. Source090 is not selected. Two confirmed folders have29 blobs/36 complete-tree entries including roots, with actual build/main.tex in each. Parent source-body reading: NONE. Metadata is navigation, not a proof interface.

Read these FIVE exact COMPLETED originals as narrow direct exceptions relative to frontier/campaigns/2026-10-14/:
'''
catalogue += '\n'.join(direct) + '''
Exact exceptions do not authorize containing namespaces, links, other source/copy bundles, role/brief/status/activity aliases or peer findings. Protected completed bodies and named metadata remain PRIVATE/local under original rights; any copies stay in your own root. No old r35 or R041 body exception propagates. No broader old-scan rerun.

'''
family = '''Your ONE developed family is SOURCE089: L1 EMBEDDINGS OF PLANAR AND BOUNDED-TREEWIDTH GRAPH METRICS, WITH THEIR FLOW-CUT INTERFACES. Both pinned manuscripts AND ALL operative source proofs are stipulated TRUE, including the formerly conjectural results. Validate exact new deductions/applicability rather than auditing upstream truth.

Confirmed canonical folders and ACTUAL wrappers:
'''
for entry in nav['families']:
    w = entry['wrapper']
    family += f"{entry['folder']}\n{w['path']}\nbytes {w['size']}; Git blob {w['sha']}.\n"
family += '''
Authenticate ALL29 canonical blobs using complete-tree size/Git blob/SHA256, including READMEs, compiled PDFs and all local objects. Read BOTH complete actual theorem/proof bodies, operative ancestors and nested includes, required companions, strongest relevant ACTUAL primary proof mechanisms and eligible ORIGINAL-history sections BEFORE extended mathematical deductions or author drafting. Follow actual include paths, not filename guesses. Distinguish proof reading from compiled/typography authentication. Recover clipped seams. Record durable mathematical understanding, exact source labels, primary versions/URLs/read extents, access failures and unread ancestry. Hashing, summaries and other agents' reading ledgers are not proof reading.

The ENTIRE source planar theorem is PAID: every finite connected planar graph with arbitrary positive real edge lengths has a real L1 embedding with one universal distortion bound. The ENTIRE bounded-treewidth theorem is PAID: for every fixed treewidth bound, every such finite weighted graph has a real L1 embedding with distortion depending only on that bound. All actual quantitative constants, weighted/cut constructions, random/relative/algorithmic operations exposed by the full proofs and companion interfaces are paid where their hypotheses match. The corresponding full multicommodity flow-cut consequences already established are paid; no discovery credit follows from merely restating the GNRS conclusions or standard metric/LP duality. Read exact source assumptions and quantitative dependencies before claiming a new interface from its title.

Standard cut-cone representations of finite L1 metrics, elementary support reduction/Caratheodory, finite-pair sampling with the actual union-bound losses, scale/weight rescaling, limits via valid contraction of zero edges, and direct flow-cut duality are paid wherever all hypotheses match. Qualitative existence, finite-dimensional realization, a relabeling of distortion, another fixed treewidth class, or elementary parameter substitutions are not nominees. A new dependence on treewidth, coherent relative construction, compositional operation, algorithmic guarantee or other conclusion requires a CLOSED identifiable nonroutine mechanism after the strongest compatible source/primary payment. Such directions are eligible, not automatically substantial. Failed shortcuts do not show all stronger known compositions fail.

Track every finite graph, arbitrary POSITIVE REAL length versus rational encoding/oracle access, connectedness, planar drawing and supplied decomposition assumptions, treewidth versus separator/minor hypotheses, terminal sets, cut measures and their common witnesses, distortion normalization, contraction/expansion order, exact versus approximate/randomized construction, support size and bit runtime. Flow/cut statements must retain the SAME capacities, arbitrary demand matrices, terminal pairs and limiting conventions actually quantified; do not swap a per-demand witness for a single all-demand embedding or a separate witness per scale for a joint budget. Directed metrics, zero/infinite capacities, disconnected cases, infinite graph limits or prescribed restrictions require their full compatibility proof and cannot be silently imported from the finite connected source headline. A discretization/sample/LP algorithm must state computation and input-access assumptions honestly.

Do not substitute unweighted graphs, favorable length ratios, bounded diameter/aspect ratio, bounded vertex count, fixed terminal pairs, restricted demand distributions, a narrower minor class, favorable decompositions, expected-only performance for a deterministic claim, or dimension/cardinality losses for a proposed FULL scope. Preserve all earlier frozen/PREFREEZE targets, including the full projection-body diagnostic and closed R162W result. When mechanisms overlap, read eligible ACTUAL original-history sections under the prospective guards; exact completed exceptions never open linked protected namespaces.

After complete operative reading, develop ONE distinct fully specified full-scope operation using sustained CONCRETE mathematics beyond a first failed composition. Try the strongest integrated source/primary reduction before naming a bridge unpaid. Preserve paid calculations, failed attempts, shared metric/cut/demand/energy budgets and exact residuals. If a viable theorem emerges, freeze exact hypotheses, all quantifiers/constants and conclusion BEFORE author-proof development, then close every interface. Otherwise give honest PREFREEZE/no nominee with precise gaps; no weaker substitute, self-grade, count, exhaustive clearance, worldwide priority or impossibility claim.

Keep source/primary/history/search/extract/render/copied bodies AND their named metadata PRIVATE/local under original rights. Before optional filename traversal or body selection beyond the direct exceptions serialize EVERY literal wildcard/substring rule below, including all r/no-r twins and role/flat/compound aliases. At most ONE correctly pruned original-history traversal, with no size/extension cutoff on eligible authored UTF8 after pruning; no projectwide rg-then-filter, broad untracked inventory or old scan rerun. Disclose false admissions, coarse omissions, reading extents, truncations/recovery, late reads and incomplete transitive ancestry. Seal YOUR own fresh exact selection ONCE, with detached FINAL/MANIFEST/outside REPORT hashes, a read-only explicit-anchor verifier and proportionate tiny COPIED own-text controls. No inherited manifest over fewer files. Artifact checks are not math gates. No nested agents, shared writes, git operations, public/browser actions or downstream formal/manuscript/release work. Parent alone commissions independent correctness and separate actual-primary substantial-contribution reviews of a viable full author proof.

'''
text = prefix + preserved + catalogue + family + isolation + '\nFurther prospective literal twins:\n*arithmetic*162y* *arithmetic*r162y*\n\n' + marker.decode() + standing.decode()
assert set(re.findall(r'\*[^\s,;()]*\*', old)) <= set(re.findall(r'\*[^\s,;()]*\*', text))
assert text.encode().split(marker, 1)[1] == standing
brief = B / 'expanded-target-2026-10-17/fresh-arithmetic-r162y-brief.txt'
assert not brief.exists()
assert not list((B / 'fresh-arithmetic-discovery-r162y').iterdir())
brief.write_text(text)
(D / 'private/completed-direct-inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')
record = {'brief': str(brief.relative_to(P)), 'bytes': len(text.encode()),
          'sha256': hashlib.sha256(text.encode()).hexdigest(), 'standing_bytes_preserved': 5570,
          'all_previous_literal_guards_retained': True, 'source': '089',
          'catalogue_extent': [147957,149459], 'canonical_blobs': 29,
          'canonical_entries_including_roots': 36, 'completed_direct_inputs': 5,
          'parent_source_body_read': False, 'publication': 'STOPPED'}
(D / 'brief-preparation.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
