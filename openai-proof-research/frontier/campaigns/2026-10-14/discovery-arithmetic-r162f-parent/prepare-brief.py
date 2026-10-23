#!/usr/bin/env python3
"""Prepare a distinct Source069 discovery; preserve all old literal guards."""
from pathlib import Path
import hashlib
import json
import re

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162f-parent'
old = (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162f-brief.txt').read_text()
marker = '--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
suffix = old.split(marker, 1)[1]
assert len(suffix.encode()) == 5570
iso = json.loads((o / 'prospective-isolation-arithmetic162g.json').read_bytes())
for peer in iso['peer_original_initial_briefs']:
    data = (p / peer['brief']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == peer['brief_sha256'] and b'*arithmetic*r162*' in data
sel = json.loads((o / 'private/catalogue-selection.json').read_bytes())
assert sel['number'] == '071' and sel['folder_count'] == 2 and sel['blob_count'] == 27
old_guards = set(re.findall(r'\*[^\s,;()]*\*', old))
guards = old_guards | {'*arithmetic*r162g*', '*arithmetic*162f*', '*arithmetic*r162f*', '*arithmetic*162e*'}
guards |= {re.sub(r'r(?=\d)', '', x) for x in guards}
substrings = old.split('Prune these case-insensitive FULL-PATH substrings before descent/read:\n', 1)[1].split('\nPrune directories BEFORE', 1)[0].strip()
brief = '''Arithmetic discovery r162g — confirmed circle-domain operative-proof discovery.
Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162g/.

Authorized Codex / GPT-6 Astra / high / default service tier. Campaign19/20,latestR041,one substantial acceptance remains. This header overrides obsolete18/20 and Factory-only lines in the COMPLETE original standing brief below. Project /home/mj-kang/Documents/Dev/math/openai-proof-research; EVERY command workdir actual PROJECT root. Every note/download/temp/copy/extract/render/scratch stays inside your unique root. No shared/old-root edits,git/staging/commit,nested agents,heavy installations,unbounded jobs or downstream formal/manuscript/release. Publication/uploads/submissions/contacts/browser UI STOPPED. Parent alone integrates, adopts grades and counts.

Read direct AGENTS.md,sources/upstream.json, EXACT acceptance bytes[4801,6347) of frontier/NEW-TEN-2026-10-14.md, and complete standing brief. No ancestor searches or journal/catalogue openings/whole-file decoding. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb AND ALL operative upstream proofs stipulated TRUE. Complete sources/preprints-tree.json has13223 entries,4858136bytes,SHAeeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b;ignore truncated tree.json. Metadata is navigation, not proof reading. Authenticate actual canonical statements/operative includes/required companions and strongest actual primary/original-history proof operations BEFORE extended deductions. Mathematics should dominate proportionate evidence work. Retain sustained concrete derivations, not just catalogue selection or a named hard gap.

This is ONE NEW DISTINCT Source071 operation, named Arithmetic162f so the ENTIRE root/brief/parent namespace is covered by *arithmetic*r162* in the ORIGINAL INITIAL brief of foreign Structural195 BEFORE this root/brief creation. Its shared status is recorded-running under another owner; this parent has not queried status or inspected live bodies/findings/activity and makes no fresh liveness claim. Exclude the whole peer namespace and every derivative alias. Do not inspect, infer or use peer mathematics. This is prompt chronology, not OS/perfect isolation or exhaustive clearance. Own162f is excluded from broad history but usable for direct own work. Old162,162b,162c,162d,162e are completed PREFREEZE/no nominee, not retried or restricted.

IMPORTANT OVERLAP: Analytic157 already carried the full Source071 circle-domain deformation comparison through arbitrary measurable Beltrami coefficients, all disk radii in l2, and strong real-analytic parameter dependence, as a paid integrated source/classical construction. Do not rename, restrict or retry that scope. A NEW nominee requires a DISTINCT closed nonroutine operation after the actual strongest source/primary/history construction. Arithmetic134's enhanced Jacquet/Levi/collision/global-period obligation and Arithmetic162f's finite-type cutoff failure also remain immutable; no old proof is retried for a desired grade. No additional family scan is authorized.

Prospective isolation BEFORE FIRST filename traversal AND BODY SELECTION beyond exact direct instructions: evaluate EVERY wildcard and substring on full-project-relative POSIX path.casefold(). Individually enumerate ALL following literal full-path wildcard guards at EVERY depth, including flat/compound/role/parent/brief/copy/derivative/status/activity aliases; every no-r twin is retained:
'''
brief += ' '.join(sorted(guards)) + '\n\nPrune these case-insensitive FULL-PATH substrings before descent/read:\n' + substrings + '\n'
brief += '''Prune directories BEFORE descent, files BEFORE byte reads/UTF8 decoding. Explicitly prune history[0-9]*,further-history-*,compound screen-*/screenNNN,role/proof-rN/check/freeze/summary/rights derivatives and toolkit/canonical-bindings/capture.py/bind.py helpers. No projectwide rg then filter, broad untracked inventory or case-insensitive O(n) asymptotic queries. Genuinely authored eligible hidden/ignored/JSON/large UTF8 INCLUDING .tex/.bib has no filesize cutoff after pruning. Coarse aliases can omit useful originals and opaque aliases can escape; disclose false admissions/coarse omissions, never claim perfect classification or exhaustive clearance. Retain publication,plain check,activity and the special *t185144-*/*k369134-* aliases prospectively. No broader old scan rerun, peer inspection or steering. Exact completed exceptions never widen a namespace.

Protected source/primary/history/search/extract/render/copied bodies AND their named metadata remain private/local under original rights. Read relevant eligible ORIGINAL-history mechanisms through the next equal/higher heading with exact extents,truncation/recovery,late reads,versions/access limits. Hashing/copying is not semantic reading. Seal YOUR OWN exact packet once, never attach an inherited manifest to a reduced selection; detached FINAL/MANIFEST/outside REPORT anchors, read-only explicit-anchor verifier and proportionate tiny copied controls. Artifact checks are not mathematical gates; administration must not displace research.

Catalogue access, if needed: ONLY direct binary seek/read sources/CONTENTS.md[122636,123890), confirmed EXACT Source071 body. Parent decoded only071 and072 numeric-title text in a bounded12000-byte window and ONLY071 body; numeric labels elsewhere are noncontiguous. Actual PDF basename is paper.pdf in both folders. No source proof body was read by parent. No child catalogue/heading locator, extra family, opening or whole read_text/readlines/read_bytes/decode. A selector failure is disclosed and grants no broader access.

Read FOUR exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/:
discovery-arithmetic-r162f-parent/assessment.md
fresh-arithmetic-discovery-r162f/packet/FINAL.md
fresh-arithmetic-discovery-r162f/packet/notes/01-operative-integration.md
fresh-arithmetic-discovery-r162f/packet/private/READING-ISOLATION.md
No containing namespace, linked body or peer status/activity access is admitted. Arithmetic162f's finite-type full-category cutoff spreading fails by rational SL2 residual-gerbe objects at unbounded HN degree; formal and infinite-localization inertia repairs do not construct a relative global equivalence. Classical/source feasibility work, no nominee. Its semantic canonical reading was eight complete blobs, not the whole equivalence proof. Arithmetic162e's all-degree specialization test fails on the ruled/Poincare family by torsion-dependent extra sections; fixed Veronese and finite etale parameter cover do not repair it. Every fibre still has degree-one nonvanishing. It is classical negative feasibility, not a substantial nominee; no alternate full positive operation closed.162d's prescribed global relative connection test fails by its mixed Atiyah class; pointwise flatification/fixed-monodromy deformation are paid. Earlier162c remains unpaid at multiplicative discrepancy retention;162b at full mixed relative Virasoro;162 at full ambient joint bi-Holder function-preserving transport;161 at defect-two Fano quantum-word elimination;160 at global contact tensor/all-sheet jets;158 at saturated2-torsion/conductor vanishing;150 at raw Kobayashi indicatrix comparison. No bodies admitted. Arithmetic122's zero-Lelong weakening is paid;127's tested degree bound fails;132's full ODP near-equality comparison remains unpaid. Structural191/192/193/194 and Arithmetic159 retain their archived PREFREEZE full scopes, no bodies admitted. Arithmetic156's whole root-stack theorem remains PASS/TECHNICAL, condition DISCHARGED, ZERO count. Arithmetic147,S183N,S182P,Analytic161/T337A161,T366A166 remain whole-scope PASS/TECHNICAL with zero count. S176A remains correctness INCOMPLETE/conditional TECHNICAL, condition UNDISCHARGED. T054L136 remains NEEDS_REPAIR/INCOMPLETE/UNRESOLVED_FULL_SCOPE_REPAIR. Every old frozen scope, PREFREEZE obligation and recovered151/152 disposition stays immutable. No restricted substitute, desired-grade retry or worldwide impossibility inference.

Your ONE developed family is SOURCE071: KOEBE CIRCLE-DOMAIN EXISTENCE AND REMOVABLE-BOUNDARY RIGIDITY. TWO canonical folders,33 descendants/27 blobs plus their roots. Authenticate ALL27 blobs by complete-tree size/Git blob/SHA256. Authentication is not semantic reading. Read BOTH README files, actual wrappers and FULL theorem interfaces, then COMPLETELY the operative proofs/includes/required companions for the developed operation, strongest actual primary antecedents and relevant eligible original history BEFORE extended deductions or author drafting. Disclose canonical bodies not semantically read. Never infer a proof operation from section names. All source and upstream operative proofs are stipulated TRUE, including historically open conclusions; validate new deductions/applicability, not upstream truth.

Confirmed wrappers:
preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/build/main.tex
bytes2396; Git blob1326543466aeda2ded4a5fbe1803cd6d349aff05.
preprints/Removable-Boundaries-and-Rigidity-of-Circle-Domains-September-23-2026/build/main.tex
bytes2529; Git blob542c691665c513b9f22b5063b41058b3b079f65a.

Follow ALL actual nested includes,ancestors,appendices/figures and complete-tree objects; no guessed wrapper. Catalogue071 already pays existence of a conformally equivalent circle domain for EVERY domain in the Riemann sphere, with arbitrary complementary-component cardinality, every component a round disk or point. The companion pays rigidity when a circle domain has CONFORMALLY REMOVABLE BOUNDARY: every conformal equivalence to another circle domain is Mobius, without a component-count restriction. These headlines AND every actual operative source construction are paid. The Lean link is navigation/scoped support, not a new author proof or permission for downstream formal work.

Read exact normalization,topological,removability,Sobolev,trace,measure and convergence hypotheses and the actual proof interfaces. Distinguish arbitrary domains from finite/countably connected classes, a conformal map on the open domain from a homeomorphic or regular extension to its boundary, round disks from point components and their accumulation, existence from a canonical normalized choice or quantitative/family stability, and conformal removability from area-zero or separate componentwise properties. The source proves the stated removability-to-rigidity direction; do not infer its converse or rigidity of every circle domain. Do not silently impose component labels,local connectivity,uniform relative separation,quasicircle/smooth boundary,positive radii or finite energy to substitute for a full proposed target. Standard Mobius normalization,Measurable Riemann Mapping consequences,group conjugacy,source/classical compositions and the old full Analytic157 deformation comparison are not nominees. Required extra regularity,extension,parameter/equivariant compatibility or quantitative constants need a CLOSED additional operation.


Develop a DISTINCT fully specified full-scope operation after the strongest integrated source/primary/history construction. Relative,structural,quantitative,hypothesis-removal or uniformity directions are not categorically excluded, but need a CLOSED identifiable nonroutine bridge at EVERY interface and must preserve all old scopes above. Carry sustained concrete calculations through strongest-payment and compatibility checks; preserve failed attempts and exact residuals. Do not stop at renaming a hard conjecture. Freeze a viable EXACT theorem BEFORE author-proof development. If nothing closes, honest PREFREEZE/no nominee with strongest integrated reduction and precise unpaid operation; no weaker substitute, exhaustive-search or global-impossibility claim.

Actual source/primary/history reading precedes extended writing; metadata,paths,abstracts,other agents' claims and hashes are not semantic reading. Record actual extents,late reads,truncations/recovery,versions/access failures,false admissions and coarse omissions. No self-grades,acceptance/count,public actions,nested agents or downstream formal/manuscript/release. Parent alone requests independent correctness and separate substantial-contribution review for a viable full author proof.

'''
brief += marker + suffix
assert old_guards <= set(re.findall(r'\*[^\s,;()]*\*', brief))
assert brief.split(marker,1)[1] == suffix
root = b/'fresh-arithmetic-discovery-r162g'
path = b/'expanded-target-2026-10-17/fresh-arithmetic-r162g-brief.txt'
assert not root.exists() and not path.exists()
root.mkdir()
path.write_text(brief)
receipt = {'brief':path.relative_to(p).as_posix(),'sha256':hashlib.sha256(brief.encode()).hexdigest(),'bytes':len(brief.encode()),'original_standing_brief_bytes':len(suffix.encode()),'old_literal_guards_retained':len(old_guards),'explicit_guards_with_twins':len(guards),'source':'071','catalogue_span':[122636,123890],'canonical_folders':2,'canonical_blobs':27,'prospective_isolation':'discovery-arithmetic-r162f-parent/prospective-isolation-arithmetic162g.json','distinct_scope':'No retry/restriction of Analytic157 paid full circle-domain deformation, or any old target'}
(o/'brief-preparation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
