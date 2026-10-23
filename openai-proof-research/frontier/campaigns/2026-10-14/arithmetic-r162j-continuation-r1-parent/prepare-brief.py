#!/usr/bin/env python3
"""Prepare distinct Source075 research with all old exclusions retained."""
from pathlib import Path
import hashlib
import json
import re

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'arithmetic-r162j-continuation-r1-parent'
old_path = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162j-brief.txt'
old = old_path.read_text()
root = b / 'fresh-arithmetic-discovery-r162k'
target = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162k-brief.txt'
assert not root.exists() and not target.exists()
iso = json.loads((o / 'prospective-isolation-arithmetic162k.json').read_bytes())
assert iso['checked_before_new_root_brief']
for peer in iso['peer_original_initial_briefs']:
    assert hashlib.sha256((p / peer['brief']).read_bytes()).hexdigest() == peer['brief_sha256']
marker = '--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = old.split(marker, 1)[1]
assert len(standing.encode()) == 5570
isolation = 'Prospective isolation BEFORE FIRST filename traversal' + old.split('Prospective isolation BEFORE FIRST filename traversal', 1)[1].split('Catalogue access, if needed:', 1)[0]
isolation = isolation.replace('\n\nPrune these case-insensitive FULL-PATH substrings', ' *arithmetic*162k* *arithmetic*r162k*\n\nPrune these case-insensitive FULL-PATH substrings', 1)
closed = 'Arithmetic162h remains CLOSED WHOLE-SCOPE' + old.split('Arithmetic162h remains CLOSED WHOLE-SCOPE', 1)[1].split('Your ONE developed family is SOURCE074:', 1)[0]
header = '''Arithmetic discovery r162k — confirmed L log L Fourier-convergence operative-proof discovery.
Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162k/.

Authorized Codex / GPT-6 Astra / reasoningEffort high / serviceTier default. Campaign19/20,latestR041,one substantial acceptance remains. This header overrides obsolete18/20 and Factory-only lines in the complete original standing brief. EVERY command workdir /home/mj-kang/Documents/Dev/math/openai-proof-research. Your root exists empty,use it directly. All notes,downloads,temp,extracts,renders,copies,scratch and seals stay inside it. No old/shared/root/brief changes,git/staging/commit,nested agents,heavy installations,unbounded jobs or downstream formal/manuscript/release. Publication/uploads/submissions/contacts/browser UI STOPPED. Parent alone integrates and adopts gates/counts.

Read direct AGENTS.md,sources/upstream.json,acceptance EXACT frontier/NEW-TEN-2026-10-14.md[4801,6347),and the complete standing brief. No ancestor search or whole journal/catalogue decoding. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb AND ALL operative upstream proofs stipulated TRUE. Complete sources/preprints-tree.json has13223entries,4858136bytes,SHAeeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b;ignore truncated tree.json. Metadata/hashes are not semantic proof reading. Actual complete source/operative includes,strongest relevant primary and original-history proof operations must be read BEFORE extended deductions or author drafting. Mathematics should dominate proportionate evidence work.

This is ONE NEW DISTINCT Source075 family,not a continuation or retry of the unpaid4D Kakeya target. Entire root/brief/future parent namespace is covered by *arithmetic*r162* in EVERY currently recorded foreign task's ORIGINAL INITIAL brief BEFORE creation. Recorded foreign status is not fresh liveness; parent queried no peer status,live body,findings or activity. Exclude every foreign namespace and derivative alias. Prompt chronology is not OS/perfect isolation or exhaustive clearance. Own162k is excluded from broad history but usable for direct own reading/writing.

Arithmetic162j continuation completed own reading of all1,019,669 canonical non-PDF bytes and named operative primary/recursive proofs,with partial companions/deep transitive limits disclosed. It remains PREFREEZE/no nominee. The full4D L4 maximal target for everyepsilon,radius,function,center and arbitrary measurable shading is UNCHANGED_UNPROVED. The conditional horizontal three-traversal operation pays exactlylambda^4 for sparse times; preparing compatible velocity/state contracts on the SAME retained projected-good mass,and normal-label,recovery/overlap costs remain unpaid. The exact combined coefficient r^4 F^(-2/s) A^(-3-2/s)/(L^3 D) and original-prior domination cannot be waived. These feasibility payments are not a frozen theorem or review grade. No restriction,renamed retry or worldwide-impossibility inference. All previous full targets and wholePASS/TECHNICAL zero-count closures remain immutable.

'''
body = '''Catalogue access, if needed: ONLY direct binary seek/read sources/CONTENTS.md[127638,128445), EXACT Source075 body. Parent decoded ONLY the first two numeric-title strings in one bounded14000-byte window and ONLY075 body. Numeric labels need not be contiguous. One confirmed folder has20descendants/17blobs plus its root. Actual wrapper is build/main.tex,compiled basename paper.pdf. Parent read NO source proof body. No child catalogue locator,scan,extra family,opening or whole-file decoding. Selector failure grants no broader access.

Read FOUR exact COMPLETED originals as narrow direct exceptions, relative to frontier/campaigns/2026-10-14/:
arithmetic-r162j-continuation-r1-parent/assessment.md
arithmetic-r162j-continuation-r1/packet/FINAL.md
arithmetic-r162j-continuation-r1/packet/private/RESEARCH.md
arithmetic-r162j-continuation-r1/packet/private/READING-ISOLATION.md
No containing namespace,linked body or peer status/activity access is admitted. The full prior target,conditional time payment,actual label/primary budgets and remaining preparation gap must be retained,not offered as a substitute or retried under another grade. Prior Analytic154 plane-direction composition paid; Analytic158 full fixed-power sparse-sampling target remains unpaid. Arithmetic162i whole original-distance-law retention/intermediate-scale/mixed-piece obligation remains unproved.

'''
family = '''Your ONE developed family is SOURCE075: ORDINARY FULL-SEQUENCE FOURIER CONVERGENCE IN L log L. Authenticate ALL17 canonical blobs against complete-tree size/Git blob/SHA256,including README,compiled PDF and every actual local object. Read actual README,wrapper,FULL theorem interfaces,then COMPLETELY the actual operative proofs/includes/required companions for the developed operation,strongest actual relevant primary proof operations and eligible ORIGINAL-history mechanisms BEFORE extended mathematics or author drafting. Follow actual nested include directives,not filename inferences. Keep durable understanding notes and recover clipped seams; paths,interfaces,abstracts,hashes and another agent's claims are not proof-body reading. Canonical complete reading must not be deferred to a later routine verification phase.

Confirmed exact folder:
preprints/Almost-everywhere-Fourier-convergence-in-L-log-L-September-23-2026
Actual wrapper:
preprints/Almost-everywhere-Fourier-convergence-in-L-log-L-September-23-2026/build/main.tex
bytes1660; Git blob94f77c6e6098b27250f820bb9ffe46caad88433c.

The full source conclusion is PAID and stipulated true: ordinary SYMMETRIC Fourier partial sums of EVERY complex-valued L log L(T) function converge almost everywhere to that function along the ENTIRE sequence. The headline and ALL actual operative source proof operations,not merely this catalogue summary,are paid input. The Lean link is navigation/scoped support,not a new theorem or authorization for downstream formalization.

Read exact Orlicz normalization,frequency/sign/truncation,measurability,pointwise exceptional-set,parameter/constant and maximal-operator hypotheses from actual proofs. Distinguish almost-everywhere convergence from uniform weak-type/norm/rate/variation control,one function from uniform families,symmetric partial sums from other summation schemes,one-parameter scalar convergence from vector/tensor/multiparameter or weighted versions,and almost-everywhere finiteness from endpoint distribution estimates. No unproved modulus,uniform majorant,endpoint bound or compatibility claim may be inferred from convergence alone. Conversely every maximal,entropy,stopping-time or other quantitative operation actually supplied by the strongest source/primary proof must receive full credit.

Do not add smoothness,positivity,extra integrability,frequency sparsity,lacunarity,separation,regular weights or a favorable function subclass to replace a proposed full target. Standard density/Banach-principle arguments,duality/interpolation,rescaling,finite sums,trivial vectorization,parameter substitutions and already-paid source/classical compositions are not substantial nominees. A failed naive extrapolation does not defeat a stronger compatible known construction. Extra quantitative,relative,weighted,variation,uniformity,hypothesis-removal or other directions are not categorically excluded,but require a CLOSED identifiable nonroutine bridge after the strongest integrated actual proof operations.

Choose and develop ONE DISTINCT fully specified full-scope operation AFTER those reads. Carry sustained concrete calculations through exact source/primary/history payment and compatibility tests,preserve genuine failed attempts and residuals. Do not stop at a renamed hard conjecture or catalogue selection. Freeze a viable EXACT theorem BEFORE author-proof development;then close every quantifier/interface. If no viable nonroutine full theorem emerges,report honest PREFREEZE/no nominee with strongest integrated derivation and precise unpaid operation,no weaker substitute,no scope change,no self-grade/count,no exhaustion/global-impossibility/priority claim. Do not commission your own agents or downstream work. Parent alone requests independent correctness and separate contribution reviews of a viable full author proof.

Disclose actual source/primary/transitive/original-history extents,versions/access failures,late reads,truncations/recovery,false admissions/coarse omissions honestly. All protected bodies AND named metadata stay private/local under original rights. Seal only YOUR new exact packet once,with fresh manifest,detached FINAL/MANIFEST/outside REPORT anchors,read-only explicit-anchor verifier and proportionate tiny COPIED own-text controls. No inherited manifest over a reduced selection. Artifact checks are not mathematical gates; administrative evidence must not displace mathematical derivation.

'''
brief = header + isolation + body + closed + family + marker + standing
old_guards = set(re.findall(r'\*[^\s,;()]*\*', old))
new_guards = set(re.findall(r'\*[^\s,;()]*\*', brief))
assert old_guards <= new_guards
assert brief.split(marker, 1)[1] == standing
root.mkdir()
target.write_text(brief)
prep = {'path': target.relative_to(p).as_posix(), 'root': root.relative_to(p).as_posix(),
        'bytes': len(brief.encode()), 'sha256': hashlib.sha256(brief.encode()).hexdigest(),
        'old_literal_guards': len(old_guards), 'new_literal_guards': len(new_guards),
        'old_guards_and_standing5570bytes_preserved': True,
        'source_label': '075', 'catalogue_extent': [127638, 128445],
        'canonical_folders': 1, 'canonical_descendants': 20, 'canonical_blobs': 17,
        'parent_operative_proof_read': False, 'foreign_initial_guard_before_creation': True}
(o / 'brief-preparation.json').write_text(json.dumps(prep, indent=2) + '\n')
args = {'clientRequestId': 'twenty-20261023-fresh-arithmetic-r162k-codex-astra-r1',
        'target': {'providerInstanceId': 'codex', 'model': 'gpt-6-astra',
                   'options': {'reasoningEffort': 'high', 'serviceTier': 'default'}},
        'mode': 'async', 'role': 'research',
        'title': 'Arithmetic162k: confirmed L log L Fourier-convergence operative-proof discovery',
        'task': brief}
(o / 'private/submitted-prompt.json').write_text(json.dumps(args, indent=2) + '\n')
print(json.dumps(prep, indent=2))
