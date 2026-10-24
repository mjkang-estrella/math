#!/usr/bin/env python3
"""Prepare a distinct pinned Source103 discovery; no dispatch or shared write."""
from pathlib import Path
import fnmatch
import hashlib
import json
import re
import subprocess

P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14'
D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162ai-parent'
R=B/'fresh-arithmetic-discovery-r162ai'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ai-brief.txt'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {g for g in re.findall(r'\*[^\s,;()]*\*',s) if g not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
raw_t=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'],cwd=P)
raw_j=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/NEW-TEN-2026-10-14.md'],cwd=P)
assert (B/'tasks.json').read_bytes()==raw_t and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()==raw_j
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P).strip()
tasks=json.loads(raw_t);assert tasks['newAccepted']==19 and tasks['target']==20
own=next(i for i,t in enumerate(tasks['tasks']) if t.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162ah-codex-astra-r1')
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,t in enumerate(tasks['tasks']):
    if i==own or t.get('status') not in {'running','queued','waiting'}:continue
    if 'brief' not in t:
        assert 'nativeTaskName' in t and 'taskId' not in t;legacy.append(i);continue
    raw=(P/t['brief']).read_bytes();patterns=rules(raw.decode())
    matches={n:[g for g in sorted(patterns) if fnmatch.fnmatchcase(n.casefold(),g.casefold())] for n in names}
    assert all(matches.values()),(i,matches)
    checks.append(dict(task_index=i,original_brief=t['brief'],sha256=sha(raw),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,legacy_limit='Historical native entries lack original briefs; no live query or reopening. Recorded status is not fresh liveness.',foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists()
N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
old_raw=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162ah-brief.txt').read_bytes()
assert sha(old_raw)=='153af514389ff21efd2e33566658f0df26686ce10415e8eaa3ef6436c35bc82a'
old=old_raw.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old_raw.split(marker,1)[1];assert len(standing)==5570
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
selected=json.loads((D/'private/intake/Source103-selection.json').read_text())
assert len(selected['folders'])==1
folder=selected['folders'][0];blobs=[x for x in selected['entries'] if x['type']=='blob']
wrapper=next(x for x in blobs if x['path']==folder+'/build/main.tex')
assert wrapper['size']==808 and wrapper['sha']=='cd8c7672e9ecd868652f0103481e0770a58ee7c3'
direct=[D/'assessment.md']+[B/'fresh-arithmetic-discovery-r162ah'/x for x in ['FINAL.md','packet/private/scope.md','packet/private/READING-LIMITS.md','packet/private/reading-record.json']]
records=[]
for p in direct:
    raw=p.read_bytes();records.append(dict(path=p.relative_to(P).as_posix(),bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw)))
dump(N/'private/completed-direct-inputs.json',records);dump(N/'private/canonical-selection.json',selected)
header='''Arithmetic discovery r162ai — confirmed logarithmic-space derandomization operative-proof discovery.
Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ai/.

Authorized Codex / GPT-6 Astra / reasoningEffort high / serviceTier default. Campaign19/20,latestR041,one substantial acceptance remains. This overrides obsolete18/20 and Factory-only lines in the complete original standing brief. EVERY command workdir /home/mj-kang/Documents/Dev/math/openai-proof-research. Your root exists empty. All scratch,temporary material,downloads,extracts,renders,copies,notes and seal stay inside it. No shared/old/brief/root changes,git/staging/commits,nested agents,heavy installs,unbounded jobs or downstream formal/manuscript/release work. Publication/uploads/submissions/contacts/browser UI STOPPED. Parent alone adopts gates/counts.

This is a FRESH DISTINCT Source103 family in a new author conversation,not another continuation or renaming of the entropy-overlap target. Read actual source and strongest operative primary/companion/history interfaces before selecting and developing a full theorem. Sustained mathematics must dominate proportionate evidence work. All source operative proofs are stipulated TRUE at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; do not audit upstream truth.

Read direct AGENTS.md,sources/upstream.json,the complete standing brief and ONLY acceptance frontier/NEW-TEN-2026-10-14.md binary bytes[4801,6347). Do not decode/hash the whole shared journal or catalogue. Complete sources/preprints-tree.json is13223 entries,4858136 bytes,SHA256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b. Ignore truncated tree.json. Metadata/authentication and other agents' ledgers are not semantic proof reading.

Before creation the parent checked new child/brief/parent paths against every current recorded T3 foreign nonterminal task's ORIGINAL INITIAL brief. Explicit broad arithmetic-r162 guards cover them. Shared recorded status is not fresh liveness. No foreign live task,findings,activity or body was queried. Own r162ai I/O is expressly authorized despite broad history exclusions; only the FIVE exact completed exceptions below admit other protected originals. No perfect-isolation/exhaustive-clearance claim follows.

Read the COMPLETE actual Source103 theorem/proof construction,including its compiler,arithmetic,controller/model,compression,estimation/fingerprint,averaging,hierarchy,implementation and conclusion interfaces and actual TeX/Bib/figure includes. Effective L=RL=BPL and the stated polynomial-time deterministic logarithmic-space compiler are ALREADY PAID. Inspect its strongest full operative proof,not just the headline. Uniformity,machine descriptions,precision,integer/rational encodings,input/time/space parameters,output/read/write conventions and simultaneous guarantees must be tracked whenever invoked. Do not silently promote language decision to an arbitrary search/sampling/streaming/interface theorem or suppress parameter costs.

Choose ONE promising full-scope operation after the strongest source/primary composition and develop it seriously. Routine class-collapse corollaries,padding,self-reduction,parameter substitutions and already supplied quantitative compiler bounds are not nominees. A failed naive reduction is not evidence that a compatible known operation cannot pay the construction. No restricted/renamed retry of an older target or desired-grade review retry. If no full result emerges,preserve concrete new derivations and precise gaps rather than claiming a difficult conjecture as a finding.

The old entropy family is archived PREFREEZE/no nominee through r162ah. FULL C stays: ONE numerical c>0 for EVERY n>=1 and EVERY independent log-concave Borel pair X,Y,including proper affine-subspace laws and points,with Sigma=CovX+CovY>0; for the ACTUAL S=X+Y and M=Sigma^(-1/2)CovX Sigma^(-1/2),Delta(S)=h(S)-n-logdetSigma/2>=c tr(M(I-M)). Preserve arbitrary within-input dependence,all spectra,one common affine normalization and the ENTIRE deficit regime. Neither C nor its negation is proved; no theorem was frozen or graded. Do NOT develop C in this distinct round or offer a Gaussian/product/controlled-Poincare/curvature/positive-spectral-floor substitute.

Its retained paid research comparisons include projection/coupling equivalence,complementary-exponential zero-deficit classification,scalar/product and proportional-covariance cases,the FULL-spectrum arbitrary-dependent Gaussian-input comparison,one source common-remainder budget,exact conditional-entropy and convex-epigraph identities,rough/singular transfer conditional on a uniform smooth estimate,and exact dependent matrix-cone/paraboloid tests. Common-flag and complementary random-allocation formulas retain every off-diagonal information cost and exact endpoint cancellation. The positive posterior curvature minimization retains conditional derivative/moving-boundary energy. The global lift recovers original covariance means only for a genuine Stein field; mixed derivatives cancel,creating no extra positive square. The paid source curvature field differs from that Stein field by an explicit source completion correction J R U_c. Standalone/output-weighted correction control and dimension-uniform original-overlap coercivity remain unpaid against ONE available entropy remainder. No source surplus may be spent twice. These are route limits,not necessary/exhaustive obstacles or counterexamples. All previous scopes/dispositions remain unchanged;the FIVE exact documents below supply bounded original context without opening prior corpora.

'''
section=f'''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[172167,173031),EXACT Source103 body. Parent read ONE bounded14000-byte window starting169969 for navigation. Initial numeric-before-bold regex failed without semantic output; recovery accidentally displayed THREE complete numeric-bold lines,including102/103/104 descriptions. Only103 full body was decoded/selected. Source102/104 operative bodies were NOT read. No child title locator,extra catalogue screen,whole-catalogue decoding or ancestor hunt. Confirmed ONE folder has{len(blobs)} blobs/{len(selected['entries'])} complete-tree entries including root. Parent source-proof body reading:NONE. This navigation limitation is disclosed,not a clearance certificate.

Confirmed canonical folder:
{folder}
ACTUAL wrapper:
{wrapper['path']}
bytes808;Git blob cd8c7672e9ecd868652f0103481e0770a58ee7c3.
Use complete-tree entries under exactly this folder for pinned raw paths. Do not guess build/manuscript or root main.tex. Authenticate actual selected objects and read every operative textual include; distinguish compiled PDF authentication from rendered/body reading.

Read these FIVE exact COMPLETED originals (project-relative POSIX paths):
'''
section+='\n'.join(x['path'] for x in records)
section+='''
These exceptions never authorize containing namespaces,links,old copied/source bundles,previous direct exceptions,role/status/brief/activity aliases or other reviews. Protected completed bodies AND their named metadata remain PRIVATE/local under original rights;copies/excerpts stay inside your own private root. No old exact exception propagates. The old entropy notes are disposition context,not the new direction.

At most ONE correctly pruned optional original-history traversal is authorized for this distinct family. Apply EVERY inherited guard/substring before descent,filename eligibility or byte reads at every depth. Query genuine authored mechanisms for logarithmic-space derandomization,randomized controllers,branching programs,uniform compilers,arithmetic/fingerprint precision and constructive output interfaces as relevant. Avoid blanket O(n)/case-insensitive scans,corpus inventories,old scan replay or reading protected derivatives. Follow eligible ORIGINAL operative hits through their equal/higher heading;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If optional traversal is not used,say so. No live peer/task/status/body query. Reading ledgers/catalogue summaries are not proof reading.

Historical full scopes and dispositions follow as CONTEXT,not permission to reopen targets or follow linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162ai* *arithmetic*r162ai*\n\n'
brief=(header+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162ai*','*arithmetic*r162ai*'}<=rules(brief.decode())
assert brief.split(marker,1)[1]==standing
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,continuation=False,distinct_family=True,source=103,catalogue_extent=[172167,173031],canonical_blobs=len(blobs),canonical_entries_including_roots=len(selected['entries']),completed_direct_inputs=5,parent_source_body_read=False,navigation_limits=selected['navigation_limits'],publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=len(blobs),canonical_entries=len(selected['entries']),both_new_literal_twins_verified=True,distinct_family=True)))
