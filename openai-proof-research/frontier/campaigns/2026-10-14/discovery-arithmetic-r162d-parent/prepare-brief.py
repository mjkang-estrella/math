#!/usr/bin/env python3
"""Prepare one distinct discovery brief; no shared indexes or source bodies read."""
from pathlib import Path
import hashlib
import json
import re

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162d-parent'
old = (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162d-brief.txt').read_text()
marker = '--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
suffix = old.split(marker, 1)[1]
assert len(suffix.encode()) == 5570
iso = json.loads((o / 'prospective-isolation-arithmetic162e.json').read_bytes())
assert iso['peer_original_initial_briefs']
for peer in iso['peer_original_initial_briefs']:
    data = (p / peer['brief']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == peer['brief_sha256']
    assert b'*arithmetic*r162*' in data
sel = json.loads((o / 'private/catalogue-selection.json').read_bytes())
assert sel['number'] == '068' and sel['folder_count'] == 7 and sel['blob_count'] == 94
old_guards = set(re.findall(r'\*[^\s,;()]*\*', old))
guards = old_guards | {'*arithmetic*r162d*', '*arithmetic*162d*', '*arithmetic*r162e*', '*arithmetic*162e*', '*structural*r195*', '*structural*195*', '*t185144-*', '*k369134-*'}
guards |= {re.sub(r'r(?=\d)', '', x) for x in guards}
substrings = old.split('Prune these case-insensitive FULL-PATH substrings before descent/read:\n', 1)[1].split('\nPrune directories BEFORE', 1)[0].strip()
header = '''Arithmetic discovery r162e — confirmed anticanonical-nonvanishing operative-proof discovery.
Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162e/.

Authorized Codex / GPT-6 Astra / high / default service tier. Campaign19/20,latestR041,one substantial acceptance remains. This header overrides obsolete18/20 and Factory-only lines in the COMPLETE original standing brief below. Project /home/mj-kang/Documents/Dev/math/openai-proof-research; EVERY command workdir actual PROJECT root. Every note/download/temp/copy/extract/render/scratch stays inside your unique root. No shared/old-root edits,git/staging/commit,nested agents,heavy installations,unbounded jobs or downstream formal/manuscript/release. Publication/uploads/submissions/contacts/browser UI STOPPED. Parent alone integrates, adopts grades and counts.

Read direct AGENTS.md,sources/upstream.json, EXACT acceptance bytes[4801,6347) of frontier/NEW-TEN-2026-10-14.md, and complete standing brief. No ancestor search, journal/catalogue openings or whole-file decoding. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb AND ALL operative upstream proofs stipulated TRUE. Complete sources/preprints-tree.json has13223 entries,4858136bytes,SHAeeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b;ignore truncated tree.json. Metadata is navigation, not proof reading. Authenticate actual canonical statements/operative includes/companions and strongest actual primary/original-history proof operations BEFORE extended deductions. Mathematics should dominate proportionate evidence work; retain durable concrete derivations, not just a source selection or renamed hard gap.

This is ONE NEW DISTINCT Source068 family, named Arithmetic162e so its ENTIRE root/brief/parent namespace is covered by the already supplied *arithmetic*r162* guard in the ORIGINAL INITIAL brief of foreign Structural195, before this root or brief was created. Structural195 is recorded-running under another owner; this parent has not queried its status or inspected live bodies/findings/activity and makes no fresh liveness claim. Exclude its entire namespace and every derivative alias. Do not inspect, infer or use peer mathematics. This is prompt chronology, not OS/perfect isolation or exhaustive historical clearance. Own162e is excluded from broad history but usable for direct own writing/reading. Old162,162b,162c,162d are completed PREFREEZE/no nominee, not retried or restricted.

Prospective isolation BEFORE FIRST filename traversal AND BODY SELECTION beyond exact direct instructions: evaluate EVERY wildcard and substring on full-project-relative POSIX path.casefold(). Individually enumerate and install ALL following literal full-path wildcard guards at EVERY depth, including flat/compound/role/parent/brief/copy/derivative/status/activity aliases; each no-r twin is explicitly retained:
'''
header += ' '.join(sorted(guards)) + '\n\nPrune these case-insensitive FULL-PATH substrings before descent/read:\n' + substrings + ' publication check activity\n'
header += '''Prune directories BEFORE descent, files BEFORE byte reads/UTF8 decoding. Also explicitly prune history[0-9]*,further-history-*,compound screen-*/screenNNN,role/proof-rN/check/freeze/summary/rights derivatives and toolkit/canonical-bindings/capture.py/bind.py helpers. No projectwide rg followed by filtering, broad untracked inventories or case-insensitive O(n) asymptotic queries. Genuinely authored eligible hidden/ignored/JSON/large UTF8 INCLUDING .tex/.bib has no filesize cutoff after pruning. Coarse aliases can omit useful originals and opaque aliases can escape; disclose false admissions and coarse omissions, never claim perfect classification/exhaustive clearance. No rerun of a broader old scan, peer inspection or steering. Exact completed exceptions never widen a namespace.

Protected source/primary/history/search/extract/render/copied bodies AND their named metadata remain private/local under original rights. Record exact original-history sections through the next equal/higher heading, extents,truncation/recovery,late reads,versions/access limits. Hashing/copying is not semantic reading. Seal YOUR OWN exact selected packet once, never attach an inherited manifest to a reduced selection; use detached FINAL/MANIFEST/outside REPORT anchors, a read-only explicit-anchor verifier and proportionate tiny copied controls. Artifact checks are not mathematical gates. Do not expand administration at the expense of research.

Catalogue access, if needed: ONLY direct binary seek/read sources/CONTENTS.md[115750,121339), confirmed EXACT Source068 body. Parent decoded only068 and069 numeric-title text in a bounded12000-byte navigation window, and ONLY068 body; no source proof body was read by parent. Numeric labels are noncontiguous. No child heading locator, catalogue scan, opening, whole read_text/readlines/read_bytes/decode, or extra family. A selector failure is disclosed and grants no broader access.

Read these FOUR exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/:
discovery-arithmetic-r162d-parent/assessment.md
fresh-arithmetic-discovery-r162d/packet/FINAL.md
fresh-arithmetic-discovery-r162d/packet/notes/01-operative-integration.md
fresh-arithmetic-discovery-r162d/packet/private/READING-ISOLATION.md
No containing namespace, linked body or peer status/activity access is admitted. Arithmetic162d's prescribed compact-parameter flat-transport test fails by a nonzero mixed relative Atiyah class for a Grassmannian/Poincare family, persisting under compatible finite etale covers; classical negative feasibility, not a substantial nominee. Pointwise flatification and fixed-monodromy deformation remain paid. No alternate positive operation closed. Earlier162c remains unpaid at uniform multiplicative discrepancy retention;162b at the full mixed relative Virasoro intertwiner;162 at full ambient joint bi-Holder function-preserving transport;161 at defect-two Fano quantum-word elimination;160 at contact tensor/all-sheet jets;158 at saturated2-torsion/conductor vanishing;150 at raw Kobayashi-indicatrix comparison. No bodies admitted. Arithmetic122's zero-Lelong weakening was already paid and its stronger finite-exponent nefness calculation unfinished; Source068 research must not rename that old scope. Arithmetic127's tested threshold/complement-to-local-degree bound fails;132's full ODP near-equality valuation comparison remains unpaid. Structural191/192/193/194 and Arithmetic159 remain archived PREFREEZE; no bodies admitted. Arithmetic156's full root-stack theorem remains closed PASS/TECHNICAL, condition DISCHARGED, ZERO count. Arithmetic147's full free-tangent surface family,S183N,S182P,Analytic161/T337A161,T366A166 remain whole-scope PASS/TECHNICAL, zero count. S176A remains correctness INCOMPLETE/conditional TECHNICAL, condition UNDISCHARGED. T054L136 remains NEEDS_REPAIR/INCOMPLETE/UNRESOLVED_FULL_SCOPE_REPAIR. Every earlier frozen scope, PREFREEZE obligation and recovered151/152 disposition stays immutable. No weaker substitute, desired-grade retry or worldwide impossibility inference.

Your ONE developed family is SOURCE068: ANTICANONICAL NONVANISHING FROM SMOOTH SEMIPOSITIVITY. SEVEN canonical companion folders,115 descendants/94 blobs plus seven roots. Authenticate ALL94 blobs against the complete pinned tree; metadata/authentication is not semantic reading. Read actual wrappers,README,FULL statements and COMPLETELY all operative proofs/includes/appendices/figures/required companions used by your operation, plus strongest actual primary and relevant eligible ORIGINAL-history mechanisms BEFORE extended deductions or author drafting. Disclose every canonical body not semantically read. Never infer operations from filenames. The seven actual wrappers are:
'''
for wrapper in sel['wrappers']:
    header += wrapper['path'] + '\nbytes' + str(wrapper['size']) + '; Git blob' + wrapper['sha'] + '.\n'
header += '''
Follow ALL actual nested includes/ancestors and complete-tree family objects; do not guess wrappers. All seven source/companion proofs are stipulated TRUE, including results formerly open. Validate NEW deductions and applicability; do not audit upstream truth.

The catalogue already pays nonvanishing of a positive anticanonical power for EVERY smooth connected complex projective variety with a smooth Hermitian semipositive anticanonical metric, in every dimension. It also explicitly pays invariant anticanonical indices on divisible progressions with the actual exponent-zero value; removal of one fixed pseudoeffective error from unbounded effective twists; bounded-metric klt-pair nonvanishing under the stated nefness/resolution/Euler-characteristic hypotheses; natural torus-invariant plurisections in the stated classes; cohomological transfer; metric descent on corrected anticanonical lines; rank-preserving contraction under its generic-section/adjoint-rank hypotheses; controlled-boundary effectivity; and the stated attainment of exact orders on curvature-null faces. These headlines AND EVERY actual operative proof construction are paid. Read exact hypotheses,quantifiers,linearizations,curvature/weight conditions,divisibility,orders and boundary conventions before use.

Distinguish smooth semipositive metrics from nefness alone, positive currents with unbounded weights, locally bounded resolution metrics, klt versus merely log canonical inputs, projective versus general compact Kahler spaces, pseudoeffective versus effective errors, untwisted versus invariant sections, natural versus arbitrary linearizations, existence in some degree versus uniform/effective index or a prescribed section, and pointwise existence versus compatible family/equivariant/relative operations. No unproved interchange of limits, valuation attainment, uniform denominators, tensor descent or metric descent is permitted. Do not infer general abundance, semiampleness, a dimension-only degree bound, hypothesis removal or family uniformity from nonvanishing. Routine products/restrictions, standard formal consequences, scalar renaming, rank bookkeeping and source/classical compositions are not nominees.

Develop a DISTINCT fully specified full-scope operation after integrating the ACTUAL complete proofs with strongest primary/original-history constructions. Relative,quantitative,structural,hypothesis-removal or uniformity directions remain available, but require a CLOSED identifiable nonroutine bridge at EVERY interface. Carry sustained concrete construction through strongest-payment and compatibility checks; preserve derivations and failed attempts. Do not stop at a named hard gap or merely rename one. Freeze a viable EXACT theorem BEFORE author-proof development. If nothing closes, honest PREFREEZE/no nominee with strongest integrated reduction and precise unpaid operation, no weaker substitute or exhaustive/global-impossibility claim.

No self-grades,acceptance/count,public action,nested agents or downstream formal/manuscript/release. Parent alone orders independent correctness and separate substantial-contribution reviews if a viable full proof is nominated. Actual reading must precede extended writing; paths,abstracts,metadata and other agents' claims are not body reading. Record late reads,truncations/recovery,actual versions,access failures,false admissions and coarse omissions honestly.

'''
brief = header + marker + suffix
assert old_guards <= set(re.findall(r'\*[^\s,;()]*\*', brief))
assert brief.split(marker, 1)[1].encode() == suffix.encode()
new_root = b / 'fresh-arithmetic-discovery-r162e'
new_brief = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162e-brief.txt'
assert not new_root.exists() and not new_brief.exists()
new_root.mkdir()
new_brief.write_text(brief)
receipt = {'brief':new_brief.relative_to(p).as_posix(),'sha256':hashlib.sha256(brief.encode()).hexdigest(),'bytes':len(brief.encode()),'original_standing_brief_bytes':len(suffix.encode()),'old_literal_guards_retained':len(old_guards),'explicit_guards_with_twins':len(guards),'source':'068','catalogue_span':[115750,121339],'canonical_folders':7,'canonical_blobs':94,'prospective_isolation':'discovery-arithmetic-r162d-parent/prospective-isolation-arithmetic162e.json'}
(o / 'brief-preparation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
