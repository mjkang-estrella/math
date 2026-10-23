#!/usr/bin/env python3
"""Prepare one distinct pinned-family discovery brief, without dispatching."""
from pathlib import Path
import hashlib
import json
import re

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
D = Path(__file__).resolve().parent
brief_path = B / 'expanded-target-2026-10-17/fresh-arithmetic-r162x-brief.txt'
old_raw = (B / 'expanded-target-2026-10-17/fresh-arithmetic-r162w-brief.txt').read_bytes()
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = old_raw.split(marker, 1)[1]
assert len(standing) == 5570
old = old_raw.decode()
prior_scopes = old[old.index('Arithmetic162v remains'):old.index('Prospective isolation BEFORE')]
isolation = old[old.index('Prospective isolation BEFORE'):old.index('Catalogue access,if needed:')]
older_dispositions = old[old.index('Arithmetic162h remains CLOSED'):old.index('Your ONE developed family')]
assert not brief_path.exists()
navigation = json.loads((D / 'private/canonical-navigation.json').read_text())
author_root = B / 'fresh-arithmetic-discovery-r162x'
assert author_root.is_dir() and not list(author_root.iterdir())
direct = [
    'arithmetic-r162w-contribution-adoption-r1/assessment.md',
    'fresh-arithmetic-discovery-r162w/FINAL.md',
    'fresh-arithmetic-discovery-r162w/packet/private/author-proof.md',
    'arithmetic-r162w-contribution-r1/packet/private/REVIEW.md',
    'arithmetic-r162w-contribution-r1/packet/private/READING-ISOLATION-LIMITS.md',
]
inputs = []
for name in direct:
    path = B / name
    raw = path.read_bytes()
    inputs.append({'path': str(path.relative_to(P)), 'bytes': len(raw),
                   'sha256': hashlib.sha256(raw).hexdigest(), 'mode': path.stat().st_mode})
header = '''Arithmetic discovery r162x — confirmed projection-body operative-proof discovery.
Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162x/.

Authorized Codex / GPT-6 Astra / reasoningEffort high / serviceTier default. Campaign 19/20, latest R041, one substantial acceptance remains. This header overrides obsolete 18/20 and Factory-only lines in the complete original standing brief. EVERY command workdir /home/mj-kang/Documents/Dev/math/openai-proof-research. Your root exists empty; use it directly. All scratch, temporary material, downloads, extracts, renders, copies, notes and seals stay inside it. No shared/old/brief/root changes, git/staging/commits, nested agents, heavy installs, unbounded jobs or downstream formal/manuscript/release work. Publication/uploads/submissions/contacts/browser UI STOPPED. Parent alone adopts gates and counts.

Read direct AGENTS.md, sources/upstream.json, acceptance EXACT frontier/NEW-TEN-2026-10-14.md[4801,6347), and the complete standing brief. Do not decode the whole journal or catalogue. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb AND ALL operative source proofs are stipulated TRUE; do not audit upstream truth. Complete sources/preprints-tree.json has 13223 entries, 4858136 bytes, SHA256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b. Ignore truncated tree.json. Metadata, hashes and others' reading ledgers are not semantic proof reading. Mathematics must dominate proportionate evidence work.

This is ONE distinct Source088 family with TWO confirmed companions. Before any namespace was created, the full child/brief/future-parent paths were checked against every current recorded foreign nonterminal task's ORIGINAL INITIAL brief; explicit arithmetic-r162 guards cover them. Shared recorded status is not fresh liveness. No live foreign task, findings, activity or body was queried. Own r162x is excluded from broad history but its own I/O is expressly authorized. No perfect-isolation or exhaustive-clearance claim follows.

R162W is CLOSED whole-scope PASS / TECHNICAL, contribution condition DISCHARGED, ZERO campaign increment. Its exact theorem is ONE smooth symplectic embedding of the ENTIRE OPEN capacity-4 ball into int(K) x int(K polar) for EVERY n>=2 and EVERY full-dimensional origin-symmetric compact convex body K, including nonsmooth bodies. Its complete compatible source/classical payment covers mixed adjacent powers and SAME momentum primitives, moving polar rows, an exponent tail chosen AFTER each next finite row count, smooth one-sided scalar choices, joint compact supports and parameter ODE/Moser construction, strict larger source balls giving compact traces in the SAME target, and exact Hamiltonian stabilization. The endpoint result is technical despite full correctness; no desired-grade retry, renaming, restricted substitute or downstream work. Width-supremum and critical-open attainment remain different statements; the latter is now paid at its full stated scope. Boundary extension, arbitrary prescribed-prefix packing and natural K-families were never claimed. Preserve all older scopes.

'''
catalogue = '''Catalogue access, if needed: ONLY binary seek/read sources/CONTENTS.md[146530,147957), EXACT Source088 body. Parent decoded only the first TWO numeric-bold titles from ONE bounded 14000-byte window, then only the selected 088 body. No child title locator, new screen, extra family, whole catalogue opening or broader catalogue decoding. Next 089 is not selected. Two actual folders have 15 blobs and 21 tree entries including roots. Parent read NO source proof body. An initial metadata lookup assumed a shallower wrapper and failed before any body read; the complete tree then confirmed the nested build/latex wrapper below. Do not infer includes from filename conventions.

Read these FIVE exact COMPLETED originals as narrow direct exceptions relative to frontier/campaigns/2026-10-14/:
'''
catalogue += '\n'.join(direct) + '''
No containing namespace, linked body, peer role, status/activity or other result access is admitted. Completed source-bearing packets and their named metadata remain PRIVATE/local; retain original rights on any exact copy inside your own root. No old r35 body/scope exception propagates. These five exact files preserve R162W's closed payment and do not authorize an old scan rerun.

'''
family = '''Your ONE developed family is SOURCE088: SHARP PROJECTION-BODY INEQUALITIES AND THE PRODUCT COUNTEREXAMPLE TO SIMPLEX MAXIMIZATION. Both pinned manuscripts and ALL operative upstream proofs are stipulated TRUE, including formerly conjectural results. Validate exact applicability and fresh deductions, not upstream truth.

Confirmed canonical folders and ACTUAL wrappers:
'''
for entry in navigation['families']:
    wrapper = entry['wrapper']
    family += f"{entry['folder']}\n{wrapper['path']}\nbytes {wrapper['size']}; Git blob {wrapper['sha']}.\n"
family += '''
Authenticate ALL 15 canonical blobs against complete-tree sizes/Git blob/SHA256, including READMEs, compiled PDFs and actual local objects. Read BOTH full actual theorem/proof bodies and every operative include, ancestor and required companion supporting the developed operation, strongest relevant ACTUAL primary proofs, and relevant eligible ORIGINAL-history sections BEFORE extended deductions or author drafting. Follow actual nested includes; distinguish mathematical proof reading from PDF/typography authentication. Recover every clipped seam. Record durable mathematical understanding and exact versions/read extents/access failures. Do not defer canonical reading until sealing or mistake source headlines for the strongest proof operations.

The entire source sharp Petty projection-volume result in all its actual dimensions, exact equality classification, and the full Lutwak-Petty inequalities actually established are PAID. The complete product-of-simplices counterexample, its actual finite-dimensional comparison, all sufficiently-large-dimension/exponential conclusions and the exact constants already derived by that proof are PAID. Read actual statements and normalization before writing formulas; do not infer constants or unstated equality cases from the catalogue. The source's proved minimization and its disproof of a proposed maximization are distinct claims. Neither authorizing former conjectures as true nor a known counterexample gives a new theorem by restatement.

Routine affine covariance and determinant changes, linear images, polarity, mixed-volume/area-measure rewritings, standard projection-body/product identities, fixed finite products, and direct gamma/Stirling asymptotics are paid wherever the actual hypotheses match. In each fixed dimension, equality plus appropriate normalized compactness already pays qualitative near-equality closeness with an unspecified modulus; do not nominate mere existence of that modulus. A sharp rate, dimension-uniform law, relative operation, stronger equality/stability or hypothesis removal needs a CLOSED identifiable nonroutine step after the strongest compatible source/primary composition. Such directions are eligible, not automatically substantial. Read strongest actual quantitative/affine/isoperimetric primary results and operative original history when mechanisms overlap.

Track full-dimensionality, symmetry versus general bodies, centering and translation invariance, projection-body versus polar-projection-body conventions, Euclidean versus affine normalization, volume powers and every dimension, fixed dimension versus dimension-uniform constants, smooth versus nonsmooth data, equality classifications, product dimensions, and common witnesses throughout approximation or limiting arguments. A failed naive route is not evidence that all stronger compositions fail. No favorable symmetry, smoothness, fixed combinatorics, restricted dimension sequence, extra moment/curvature bound or easier centering may silently replace a proposed FULL scope. All previous frozen/PREFREEZE obligations remain immutable.

After full operative reading choose and develop ONE distinct fully specified full-scope operation, carrying sustained CONCRETE mathematics beyond a first failed shortcut. Try the strongest integrated payment before declaring a bridge unpaid. Preserve calculations, failed attempts, compatible source/classical payments and precise residuals. Freeze a viable exact theorem BEFORE author-proof development, then close every quantifier/interface. If no result closes, report PREFREEZE/no nominee with precise gaps, without a weaker substitute, self-grade, count, exhaustive clearance, global impossibility or priority claim. A difficult unproved target is not a finding.

Keep all protected source/primary/history/search/render/copy bodies AND named metadata PRIVATE/local under original rights. Prospectively serialize the full literal guards and substring rules below before optional filename traversal/body selection beyond the direct exceptions. Do at most ONE correctly pruned original-history traversal if needed, with no size/extension cutoff after pruning and no projectwide rg-then-filter; disclose false admissions, coarse omissions, truncations, recoveries, late reads and unread transitive ancestry. No peer inspection/steering or old scan rerun. Seal YOUR OWN exact fresh packet ONCE at the end with detached FINAL/MANIFEST/outside REPORT anchors, a read-only explicit-anchor verifier and proportionate tiny COPIED own-text controls. Do not attach an inherited manifest to a reduced selection. Artifact checks are not mathematical gates. No nested agents, shared writes, public actions or downstream work. Parent alone commissions independent correctness and separate substantial-contribution reviews of a viable full author proof.

'''
extra = '\nAdditional prospective literal wildcard twins for the new round and completed role namespaces:\n*arithmetic*162x* *arithmetic*r162x* *arithmetic*162w*proof* *arithmetic*r162w*proof* *arithmetic*162w*contribution* *arithmetic*r162w*contribution*\n\n'
text = header + prior_scopes + older_dispositions + catalogue + family + isolation + extra + marker.decode() + standing.decode()
new_patterns = re.findall(r'\*[^\s,;()]*\*', text)
old_patterns = re.findall(r'\*[^\s,;()]*\*', old_raw.decode())
assert set(old_patterns) <= set(new_patterns)
assert text.encode().split(marker, 1)[1] == standing
brief_path.write_text(text)
(D / 'private/completed-direct-inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')
(D / 'brief-preparation.json').write_text(json.dumps({
    'brief': str(brief_path.relative_to(P)), 'bytes': len(text.encode()),
    'sha256': hashlib.sha256(text.encode()).hexdigest(), 'standing_bytes_preserved': 5570,
    'all_previous_literal_guards_retained': True, 'new_literal_twins_added': 6,
    'source': '088', 'catalogue_extent': [146530, 147957],
    'canonical_blobs': 15, 'canonical_entries_including_roots': 21,
    'source_body_read_by_parent': False, 'completed_direct_inputs': len(inputs),
    'new_theorem_or_gate_assigned': False, 'publication': 'STOPPED',
}, indent=2) + '\n')
print(json.dumps({'brief': str(brief_path.relative_to(P)), 'bytes': len(text.encode()),
                  'source': '088', 'standing_bytes': 5570, 'direct_completed_inputs': len(inputs)}))
