#!/usr/bin/env python3
"""Prepare one distinct Source074 task, retaining every inherited guard."""
from pathlib import Path
import hashlib
import json
import re

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162i-parent'
previous = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162i-brief.txt'
target = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162j-brief.txt'
root = b / 'fresh-arithmetic-discovery-r162j'
old = previous.read_text()
marker = '--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = old.split(marker, 1)[1]
assert len(standing.encode()) == 5570
assert not root.exists() and not target.exists()
iso = json.loads((o / 'prospective-isolation-arithmetic162j.json').read_bytes())
assert iso['checked_before_new_root_or_brief']
for peer in iso['peer_original_initial_briefs']:
    assert hashlib.sha256((p / peer['brief']).read_bytes()).hexdigest() == peer['brief_sha256']
header = old.split('Prospective isolation BEFORE FIRST filename traversal', 1)[0]
header = header.replace('r162i', 'r162j').replace('Arithmetic162i', 'Arithmetic162j')
header = header.replace('Own162i', 'Own162j').replace('Source073', 'Source074')
header = header.replace('confirmed Falconer-distance operative-proof discovery', 'confirmed three/four-dimensional Kakeya operative-proof discovery')
isolation = 'Prospective isolation BEFORE FIRST filename traversal' + old.split('Prospective isolation BEFORE FIRST filename traversal', 1)[1].split('Catalogue access, if needed:', 1)[0]
isolation = isolation.replace('\n\nPrune these case-insensitive FULL-PATH substrings', ' *arithmetic*162j* *arithmetic*r162j*\n\nPrune these case-insensitive FULL-PATH substrings', 1)
body = '''Catalogue access, if needed: ONLY direct binary seek/read sources/CONTENTS.md[126238,127638), confirmed EXACT Source074 body. Parent decoded only the first two numeric-title strings in a bounded14000-byte window and ONLY074 body. Numeric labels need not be contiguous. Two confirmed folders have41 descendants/35 blobs plus their two roots. Both actual wrappers are build/paper.tex; compiled basenames paper.pdf. Parent read NO source proof body. No child catalogue locator,scan,extra family,opening or whole-file decoding. A selector failure is disclosed and grants no broader access.

Read FOUR exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/:
discovery-arithmetic-r162i-parent/assessment.md
fresh-arithmetic-discovery-r162i/packet/FINAL.md
fresh-arithmetic-discovery-r162i/packet/PREFREEZE.md
fresh-arithmetic-discovery-r162i/packet/private/READING-ISOLATION.md
No containing namespace,linked body or peer status/activity access is admitted. The full previous Falconer whole-law target remains UNCHANGED_UNPROVED: fixed-filter Besov/Lp deductions are paid; uniform near-full-mass retention with polynomial loss cost, intermediate near-plane scales and mixed-piece interactions remain unpaid. Its spike/thin-slab diagnostics do NOT refute the full distance-law target. Do not restrict,rename or retry that target here.

Arithmetic162h remains CLOSED WHOLE-SCOPE PASS/TECHNICAL, contribution condition DISCHARGED, ZERO count for the full uniform squared compact C^m exponent1/4 theorem,one universal Borel choice,complete critical Cauchy law. Its entire technical reduction is closed input; no grade shopping or downstream work. Prior162g countable-contact connectors with arbitrary L2 costs,162f relative global equivalence,162e all-degree specialization,162d prescribed relative connection,162c multiplicative discrepancy,162b mixed relative Virasoro,162 full nonzero Milnor-level transport,161 quantum residual,160 all-sheet contact jets,158 saturated arithmetic and150 raw indicatrix obligations retain their full archives. Arithmetic134 Jacquet/Levi/collision/global periods remain unpaid. Arithmetic156,Arithmetic147,S183N,S182P,Analytic161/T337A161,T366A166 and162h remain whole-scope PASS/TECHNICAL with correctness condition DISCHARGED,ZERO count. S176A correctness INCOMPLETE/conditional TECHNICAL remains condition UNDISCHARGED. T054L136 remains NEEDS_REPAIR/INCOMPLETE/UNRESOLVED_FULL_SCOPE_REPAIR. Every prior frozen/PREFREEZE scope and recovered151/152 disposition stays immutable.

Your ONE developed family is SOURCE074: THREE-DIMENSIONAL KAKEYA MAXIMAL AND FOUR-DIMENSIONAL HAUSDORFF KAKEYA. Authenticate ALL35 canonical blobs against complete-tree size/Git blob/SHA256, including READMEs,compiled PDFs and every actual local object. Authentication is not semantic reading. Read both actual READMEs,wrappers,FULL theorem interfaces, then COMPLETELY the actual operative proofs/includes/required companions supporting the developed operation,strongest actual primary antecedents and relevant eligible original-history mechanisms BEFORE extended deductions or author drafting. Disclose unread canonical/primary/transitive bodies, including typography not operative. Follow actual include directives, not file-name inferences.

Confirmed exact folder and wrapper bindings:
preprints/Every-four-dimensional-Kakeya-set-has-full-Hausdorff-dimension-September-24-2026
preprints/Every-four-dimensional-Kakeya-set-has-full-Hausdorff-dimension-September-24-2026/build/paper.tex
bytes2820; Git blob68cc2974f85d66d5d91ae6a9d74e68a6d65864c8.
preprints/The-Kakeya-maximal-conjecture-in-three-dimensions-September-23-2026
preprints/The-Kakeya-maximal-conjecture-in-three-dimensions-September-23-2026/build/paper.tex
bytes865; Git blob0fc22149aa914e9b5b0e87677c1e5a7f45fee8ee.

Both headline conclusions AND EVERY actual operative source proof operation are stipulated TRUE and paid: for each epsilon>0 the three-dimensional unit-tube maximal operator has L3(R3)->L3(S2) norm O_epsilon(delta^(-epsilon)); every subset of R4 containing a unit segment in every direction has Hausdorff dimension4, without compactness/regularity assumptions on the set or witnessing line family. Do not audit upstream truth or nominate a source conclusion.

Prior Analytic154's integrated K3 plus Bright-Dhar flag and Hera counting argument already pays the s+t/2 plane-direction bound in R4. Prior Analytic158 already pays near-full temporal sampling and density-shift cancellation; its full fixed-power sparse-sampling target remains unclosed even with K3 maximal control. These are immutable dispositions, not authorization to open their protected namespaces or to offer restricted/renamed replacements. Relevant older eligible ORIGINAL-history overlaps still require actual body reading through the next equal/higher heading under the prospective guards. Summaries are not body reading. Do not infer a worldwide impossibility from any failed route.

Read exact dimensional,directional,tube-length/radius,multiplicity,density,measurability,scale/epsilon and constant quantifiers in the actual operative proofs. Retain Euclidean straight-line geometry unless a NEW proved operation genuinely carries every geometric and analytic interface to another setting. Distinguish full Hausdorff dimension from quantitative content/positive measure,maximal norm from fixed finite-tube counting,all directions from favorable subsets,epsilon losses from an endpoint,arbitrary witnessing line families from regular parametrizations,and scale-dependent estimates from uniform families. Do not silently replace a full target by compactness,Ahlfors regularity,transversality,separation,product form or smooth directional data. Ordinary interpolation,duality,rescaling,finite-union/Fubini arguments,parameter substitutions and already-paid strongest proof compositions do not establish substantial contribution.

After reading the strongest integrated construction, develop ONE DISTINCT fully specified full-scope operation with a CLOSED identifiable nonroutine bridge. Quantitative,relative,weighted,stability,hypothesis-removal or other directions are not categorically excluded, but no title-based conjecture or renamed prior gap is a result. Try compatible strongest known operations,carry concrete sustained calculations beyond the first failed shortcut,preserve exact interfaces and failures. Do not stop at catalogue selection or return an unproved hard target as a nominee. Freeze a viable EXACT theorem BEFORE author-proof development. If nothing closes,honest PREFREEZE/no nominee with the strongest integrated reduction,precise unpaid operation and unchanged original target;no weaker substitute,self-grade,count,exhaustion or global-impossibility claim.

Actual source/primary/original-history body reading precedes extended writing; filenames,abstracts,metadata,hashes and another agent's claims are not semantic reading. Record actual extents,versions,late reads,truncations/recovery,access failures,false admissions/coarse omissions honestly. Mathematics should dominate proportionate evidence work. No public actions,nested agents,shared writes or downstream formal/manuscript/release. Parent alone requests independent correctness and separate substantial-contribution reviews of a viable full author proof.

'''
brief = header + isolation + body + marker + standing
old_guards = set(re.findall(r'\*[^\s,;()]*\*', old))
new_guards = set(re.findall(r'\*[^\s,;()]*\*', brief))
assert old_guards <= new_guards
assert brief.split(marker, 1)[1] == standing
assert '*t185144-*' in new_guards and '*k369134-*' in new_guards
root.mkdir()
target.write_text(brief)
prep = {'path': target.relative_to(p).as_posix(), 'root': root.relative_to(p).as_posix(),
        'bytes': len(brief.encode()), 'sha256': hashlib.sha256(brief.encode()).hexdigest(),
        'old_literal_guards': len(old_guards), 'new_literal_guards': len(new_guards),
        'all_old_guards_retained': True, 'standing_suffix_bytes_unchanged': 5570,
        'source_label': '074', 'source_catalogue_extent': [126238, 127638],
        'canonical_folders': 2, 'canonical_descendants': 41, 'canonical_blobs': 35,
        'parent_operative_proof_read': False,
        'prospective_foreign_initial_guard_checked_before_creation': True}
(o / 'brief-preparation.json').write_text(json.dumps(prep, indent=2) + '\n')
args = {'clientRequestId': 'twenty-20261022-fresh-arithmetic-r162j-codex-astra-r1',
        'target': {'providerInstanceId': 'codex', 'model': 'gpt-6-astra',
                   'options': {'reasoningEffort': 'high', 'serviceTier': 'default'}},
        'mode': 'async', 'role': 'research',
        'title': 'Arithmetic162j: confirmed three/four-dimensional Kakeya operative-proof discovery',
        'task': brief}
(o / 'private/submitted-prompt.json').write_text(json.dumps(args, indent=2) + '\n')
print(json.dumps(prep, indent=2))
