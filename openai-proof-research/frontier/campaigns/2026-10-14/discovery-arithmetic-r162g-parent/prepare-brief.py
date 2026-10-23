#!/usr/bin/env python3
"""Prepare a distinct Source069 discovery; preserve all old literal guards."""
from pathlib import Path
import hashlib
import json
import re

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162g-parent'
old = (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162g-brief.txt').read_text()
marker = '--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
suffix = old.split(marker, 1)[1]
assert len(suffix.encode()) == 5570
iso = json.loads((o / 'prospective-isolation-arithmetic162h.json').read_bytes())
for peer in iso['peer_original_initial_briefs']:
    data = (p / peer['brief']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == peer['brief_sha256'] and b'*arithmetic*r162*' in data
sel = json.loads((o / 'private/catalogue-selection.json').read_bytes())
assert sel['number'] == '072' and sel['folder_count'] == 2 and sel['blob_count'] == 25
old_guards = set(re.findall(r'\*[^\s,;()]*\*', old))
guards = old_guards | {'*arithmetic*r162h*', '*arithmetic*162f*', '*arithmetic*r162g*', '*arithmetic*162e*'}
guards |= {re.sub(r'r(?=\d)', '', x) for x in guards}
substrings = old.split('Prune these case-insensitive FULL-PATH substrings before descent/read:\n', 1)[1].split('\nPrune directories BEFORE', 1)[0].strip()
brief = '''Arithmetic discovery r162h — confirmed Brennan/integral-means operative-proof discovery.
Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162h/.

Authorized Codex / GPT-6 Astra / high / default service tier. Campaign19/20,latestR041,one substantial acceptance remains. This header overrides obsolete18/20 and Factory-only lines in the COMPLETE original standing brief below. Project /home/mj-kang/Documents/Dev/math/openai-proof-research; EVERY command workdir actual PROJECT root. Every note/download/temp/copy/extract/render/scratch stays inside your unique root. No shared/old-root edits,git/staging/commit,nested agents,heavy installations,unbounded jobs or downstream formal/manuscript/release. Publication/uploads/submissions/contacts/browser UI STOPPED. Parent alone integrates, adopts grades and counts.

Read direct AGENTS.md,sources/upstream.json, EXACT acceptance bytes[4801,6347) of frontier/NEW-TEN-2026-10-14.md, and complete standing brief. No ancestor searches or journal/catalogue openings/whole-file decoding. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb AND ALL operative upstream proofs stipulated TRUE. Complete sources/preprints-tree.json has13223 entries,4858136bytes,SHAeeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b;ignore truncated tree.json. Metadata is navigation, not proof reading. Authenticate actual canonical statements/operative includes/required companions and strongest actual primary/original-history proof operations BEFORE extended deductions. Mathematics should dominate proportionate evidence work. Retain sustained concrete derivations, not just catalogue selection or a named hard gap.

This is ONE NEW DISTINCT Source072 operation, named Arithmetic162f so the ENTIRE root/brief/parent namespace is covered by *arithmetic*r162* in the ORIGINAL INITIAL brief of foreign Structural195 BEFORE this root/brief creation. Its shared status is recorded-running under another owner; this parent has not queried status or inspected live bodies/findings/activity and makes no fresh liveness claim. Exclude the whole peer namespace and every derivative alias. Do not inspect, infer or use peer mathematics. This is prompt chronology, not OS/perfect isolation or exhaustive clearance. Own162f is excluded from broad history but usable for direct own work. Old162,162b,162c,162d,162e,162f,162g are completed PREFREEZE/no nominee, not retried or restricted.

IMPORTANT OVERLAP: Arithmetic162g's full countable-contact modulus operation for arbitrary removable dust, arbitrary continua meeting it and arbitrary L2 costs remains unpaid at its uniform local connector bridge. Do not rename, restrict or retry it. Analytic157's full circle-domain measurable-Beltrami/deformation comparison is already paid. Arithmetic134's enhanced Jacquet/Levi/collision/global-period scope and every earlier frozen statement remain immutable. A NEW nominee needs a DISTINCT closed nonroutine operation after the actual strongest source/primary/history construction. No desired-grade retry and no additional family scan is authorized.

Prospective isolation BEFORE FIRST filename traversal AND BODY SELECTION beyond exact direct instructions: evaluate EVERY wildcard and substring on full-project-relative POSIX path.casefold(). Individually enumerate ALL following literal full-path wildcard guards at EVERY depth, including flat/compound/role/parent/brief/copy/derivative/status/activity aliases; every no-r twin is retained:
'''
brief += ' '.join(sorted(guards)) + '\n\nPrune these case-insensitive FULL-PATH substrings before descent/read:\n' + substrings + '\n'
brief += '''Prune directories BEFORE descent, files BEFORE byte reads/UTF8 decoding. Explicitly prune history[0-9]*,further-history-*,compound screen-*/screenNNN,role/proof-rN/check/freeze/summary/rights derivatives and toolkit/canonical-bindings/capture.py/bind.py helpers. No projectwide rg then filter, broad untracked inventory or case-insensitive O(n) asymptotic queries. Genuinely authored eligible hidden/ignored/JSON/large UTF8 INCLUDING .tex/.bib has no filesize cutoff after pruning. Coarse aliases can omit useful originals and opaque aliases can escape; disclose false admissions/coarse omissions, never claim perfect classification or exhaustive clearance. Retain publication,plain check,activity and the special *t185144-*/*k369134-* aliases prospectively. No broader old scan rerun, peer inspection or steering. Exact completed exceptions never widen a namespace.

Protected source/primary/history/search/extract/render/copied bodies AND their named metadata remain private/local under original rights. Read relevant eligible ORIGINAL-history mechanisms through the next equal/higher heading with exact extents,truncation/recovery,late reads,versions/access limits. Hashing/copying is not semantic reading. Seal YOUR OWN exact packet once, never attach an inherited manifest to a reduced selection; detached FINAL/MANIFEST/outside REPORT anchors, read-only explicit-anchor verifier and proportionate tiny copied controls. Artifact checks are not mathematical gates; administration must not displace research.

Catalogue access, if needed: ONLY direct binary seek/read sources/CONTENTS.md[123890,125448), confirmed EXACT Source072 body. Parent decoded only the first two numeric-title texts in a bounded14000-byte window and ONLY072 body; numeric labels need not be contiguous. Both actual PDF basenames are paper.pdf. No source proof body was read by parent. No child heading locator,catalogue scan,extra family,opening or whole read_text/readlines/read_bytes/decode. A selector failure is disclosed and grants no broader access.

Read FOUR exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/:
discovery-arithmetic-r162g-parent/assessment.md
fresh-arithmetic-discovery-r162g/packet/FINAL.md
fresh-arithmetic-discovery-r162g/packet/notes/01-operative-integration.md
fresh-arithmetic-discovery-r162g/packet/private/READING-ISOLATION.md
No containing namespace, linked body or peer status/activity access is admitted. Arithmetic162g remains PREFREEZE at the uniform countable-contact connector construction for arbitrary continua meeting removable dust with arbitrary L2 weighted costs. The buffered-anchor calculation and explicit failed shortcuts do not close or disprove its full target. All25 canonical textual bodies were read there; no nominee or grade. Arithmetic162f's finite-type full-category cutoff spreading fails by rational SL2 residual-gerbe objects at unbounded HN degree; formal and infinite-localization inertia repairs do not construct a relative global equivalence. Classical/source feasibility work, no nominee. Its semantic canonical reading was eight complete blobs, not the whole equivalence proof. Arithmetic162e's all-degree specialization test fails on the ruled/Poincare family by torsion-dependent extra sections; fixed Veronese and finite etale parameter cover do not repair it. Every fibre still has degree-one nonvanishing. It is classical negative feasibility, not a substantial nominee; no alternate full positive operation closed.162d's prescribed global relative connection test fails by its mixed Atiyah class; pointwise flatification/fixed-monodromy deformation are paid. Earlier162c remains unpaid at multiplicative discrepancy retention;162b at full mixed relative Virasoro;162 at full ambient joint bi-Holder function-preserving transport;161 at defect-two Fano quantum-word elimination;160 at global contact tensor/all-sheet jets;158 at saturated2-torsion/conductor vanishing;150 at raw Kobayashi indicatrix comparison. No bodies admitted. Arithmetic122's zero-Lelong weakening is paid;127's tested degree bound fails;132's full ODP near-equality comparison remains unpaid. Structural191/192/193/194 and Arithmetic159 retain their archived PREFREEZE full scopes, no bodies admitted. Arithmetic156's whole root-stack theorem remains PASS/TECHNICAL, condition DISCHARGED, ZERO count. Arithmetic147,S183N,S182P,Analytic161/T337A161,T366A166 remain whole-scope PASS/TECHNICAL with zero count. S176A remains correctness INCOMPLETE/conditional TECHNICAL, condition UNDISCHARGED. T054L136 remains NEEDS_REPAIR/INCOMPLETE/UNRESOLVED_FULL_SCOPE_REPAIR. Every old frozen scope, PREFREEZE obligation and recovered151/152 disposition stays immutable. No restricted substitute, desired-grade retry or worldwide impossibility inference.

Your ONE developed family is SOURCE072: BRENNAN AND THE INTEGRAL-MEANS SPECTRUM. TWO canonical folders,33 descendants/25 blobs plus their roots. Authenticate ALL25 blobs by complete-tree size/Git blob/SHA256. Authentication is not semantic reading. Read BOTH README files, actual wrappers and FULL theorem interfaces, then COMPLETELY the operative proofs/includes/required companions for the developed operation, strongest actual primary antecedents and relevant eligible original history BEFORE extended deductions or author drafting. Disclose canonical bodies not semantically read. Never infer proof operations from section names. All source and upstream operative proofs are stipulated TRUE, including historically open conclusions; validate new deductions/applicability, not upstream truth.

Confirmed wrappers:
preprints/Brennans-conjecture-and-sharp-inverse-square-integral-means-September-24-2026/build/main.tex
bytes2123; Git blobec4d2a0f67cd877d95c6d7be7775a4e74844e844.
preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/build/main.tex
bytes1914; Git blob3a7100c0fe2186a2a4deefd37af6e1764b788328.

Follow ALL actual nested includes,ancestors,appendices/figures and complete-tree objects; no guessed wrapper. The catalogue already pays Brennan: for EVERY conformal bijection phi from a simply connected plane domain onto the disk, |phi-prime|^s is area-integrable for 4/3<s<4. It also pays the sharp schlicht-class inverse-square exponent B_S(-2)=1 and the universal identity B_S(t)=|t|-1 for t<=-2, as well as a uniform inverse-first-power upper exponent strictly below1/4 and consequently B_b(-1)<1/4 for the bounded universal spectrum, refuting Kraetzer at that parameter. These headlines AND every actual operative source construction are paid. Read exact normalizations,class definitions,uniform constants and quantifiers in BOTH proofs; do not conflate the schlicht and bounded classes or infer an unstated explicit strict gap from catalogue wording. The Lean link is navigation/scoped support, not a new author proof or permission for downstream work.

Distinguish an open integrability range from its endpoints, ordinary area integrability from weak/Lorentz/Orlicz estimates, bounds for a fixed map from uniform normalized-class bounds, inverse-map derivative identities from an additional theorem, and radial integral means from arbitrary boundary or Whitney estimates. Retain domain/target normalization, possible unbounded domains,Jacobian powers and actual uniformity when transporting between a map and its inverse. Do not assume boundary regularity,quasidisk hypotheses,finiteness of boundary length or a map-dependent constant to substitute for a proposed full universal operation. Convexity/interpolation,standard Holder/Fubini/change-of-variable consequences,parameter substitution and source/classical compositions are not nominees. Endpoint improvements,sharp constants,stability,equality/extremal structure or relative/multifractal refinements need a CLOSED additional operation, with every compatibility and exponent paid. Do not turn a formerly open source conclusion into a new-to-project acceptance by renaming it.


Develop a DISTINCT fully specified full-scope operation after the strongest integrated source/primary/history construction. Relative,structural,quantitative,hypothesis-removal or uniformity directions are not categorically excluded, but need a CLOSED identifiable nonroutine bridge at EVERY interface and must preserve all old scopes above. Carry sustained concrete calculations through strongest-payment and compatibility checks; preserve failed attempts and exact residuals. Do not stop at renaming a hard conjecture. Freeze a viable EXACT theorem BEFORE author-proof development. If nothing closes, honest PREFREEZE/no nominee with strongest integrated reduction and precise unpaid operation; no weaker substitute, exhaustive-search or global-impossibility claim.

Actual source/primary/history reading precedes extended writing; metadata,paths,abstracts,other agents' claims and hashes are not semantic reading. Record actual extents,late reads,truncations/recovery,versions/access failures,false admissions and coarse omissions. No self-grades,acceptance/count,public actions,nested agents or downstream formal/manuscript/release. Parent alone requests independent correctness and separate substantial-contribution review for a viable full author proof.

'''
brief += marker + suffix
assert old_guards <= set(re.findall(r'\*[^\s,;()]*\*', brief))
assert brief.split(marker,1)[1] == suffix
root = b/'fresh-arithmetic-discovery-r162h'
path = b/'expanded-target-2026-10-17/fresh-arithmetic-r162h-brief.txt'
assert not root.exists() and not path.exists()
root.mkdir()
path.write_text(brief)
receipt = {'brief':path.relative_to(p).as_posix(),'sha256':hashlib.sha256(brief.encode()).hexdigest(),'bytes':len(brief.encode()),'original_standing_brief_bytes':len(suffix.encode()),'old_literal_guards_retained':len(old_guards),'explicit_guards_with_twins':len(guards),'source':'072','catalogue_span':[123890,125448],'canonical_folders':2,'canonical_blobs':25,'prospective_isolation':'discovery-arithmetic-r162g-parent/prospective-isolation-arithmetic162h.json','distinct_scope':'New Source072 operation; no retry/restriction of Arithmetic162g connector bridge or other old target'}
(o/'brief-preparation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
