"""Root documentary verification of r525 (zero qualified survivors) and preparation of the second adversarial qualification of 382297. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r525';S1=P/'transitive-bunkbed-source-review-r1';C=P/'expanded-corpus-r334';V=P/'parking-strong-a2-primary-qualification-sol-r2';L=P/'transitive-bunkbed-primary-qualification-sol-r2';assert not L.exists()

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==212 and m['accepted_credit']==0
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=m['terminal_noncircular_self_exclusions'];assert set(aex)=={'MANIFEST.json','seal_lane.receipt.json','seal_lane.output.txt'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r525.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'literal-provenance.json');assert len(ids)==len(prov)==len(gates)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
sources={}
for key,v in prov.items():
 raw,obj,token=corpus(v);assert (A/gates[key]['literal_file']).read_bytes()==raw and obj['mathdb_id']==int(key)
 assert token.decode()==v['statement_token'] and dg(token)==v['token_sha256'] and dg(obj['statement'].encode())==v['decoded_sha256'];sources[key]=obj['source_url']
assert all(str(v['credit'])=='0' for v in gates.values())
abudget=search(A,3,9,3,9,['search-one-response.json','search-two-response.json','search-three-response.json'])
ae=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=7,success=7),7)
hist=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(hist)==len(allow)==919 and {x['path'] for x in hist}==set(allow)
for x in hist:
 rel=Path(x['path']).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482,526]) and 'lean-address' not in x['path']
assert (A/'FULLCANDIDATE.md').is_file() and (A/'DORMANT-SOL-FORMAL-PLAN.md').is_file()

src=[S1/'literal-target.json',S1/'literal-target.jsonl',S1/'target-provenance.json',S1/'REVIEW.md',S1/'382297review.json',S1/'source-read-inventory.json',C/'CANDIDATE.md',P/'transitive-bunkbed-semantic-plan-review-r3/REVIEW.md',P/'transitive-bunkbed-semantic-review-parent-adjudication-r3.json',P/'transitive-bunkbed-parent-qualification-r1.json',P/'transitive-bunkbed-new-indicators-formal-pi-r19/src/BunkbedBase.lean',V/'inputs/accepted57-scopes.json',V/'inputs/prior39-scopes.json']
for q in src:assert q.is_file(),q
papers=['bunkbed','bunkbed-journal','bunkbed-acyclic','bunkbed-acyclic-v1','bunkbed-complete','bunkbed-complete-correct','bunkbed-leander','bunkbed-thesis','bunkbed-abs','bunkbed-acyclic-abs']
for n in papers:assert (C/(n+'.txt')).is_file() and (C/(n+'.bytes')).is_file(),n
assert (C/'bunkbed.clean.txt').is_file()

ass='r525 zero qualified survivors, no formal dispatch. 360614: an author-complete negation of the printed statement, H=K12,12,k3 with B=K3m,3m for m>=176 beating balanced T3 by a uniform ratio; the author records a serious fewer-parts and domain-correction objection and recommends no significant survivor, and root does not route it for review. 382200 has a source-definition mismatch and a zero-credit recommendation. 361014 lacks a sharp global parity-compatible decomposition lemma and quasirandom stability. 333517 lacks a denser atom or sharp general upper theorem. Sixteen assigned source works unread; recorded parks are not open-status certifications. Verified 212 manifest files, 20 corpus bindings, 13 frozen, 919 saved history entries, 7 GET successes (all PDF), 3 searches / 9 strings with responses saved. Credit 0, 57/80.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=212,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=919,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS_AUTHOR_COMPLETE_360614_NOT_ROUTED_DOMAIN_CORRECTION_OBJECTION',credit=0,accepted_new=57,terminal_self_exclusions=sorted(aex),root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r557.json');den['utc']=now;den['root_r525_scope']=ass
save(P/'expanded-corpus-r525-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r558.json';save(denpath,den)

L.mkdir();(L/'inputs').mkdir();(L/'inputs/sources').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(V/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
rename={'literal-target.json':'literal382297.json','literal-target.jsonl':'original382297.raw.jsonl','target-provenance.json':'provenance382297.json','REVIEW.md':None,'382297review.json':'review-r1-382297review.json','source-read-inventory.json':'review-r1-source-read-inventory.json','CANDIDATE.md':'author-CANDIDATE.md','BunkbedBase.lean':'lean-definitions-BunkbedBase.lean','accepted57-scopes.json':'accepted57-scopes.json','prior39-scopes.json':'prior39-scopes.json'}
for q in src:
 if q.parent==S1 and q.name=='REVIEW.md':n='review-r1-REVIEW.md'
 elif q.parent.name=='transitive-bunkbed-semantic-plan-review-r3':n='semantic-plan-REVIEW.md'
 else:n=rename.get(q.name,q.name)
 shutil.copyfile(q,L/'inputs'/n)
for n in papers:
 for ext in ['.txt','.bytes']:shutil.copyfile(C/(n+ext),L/'inputs/sources'/(n+ext))
shutil.copyfile(C/'bunkbed.clean.txt',L/'inputs/sources/bunkbed.clean.txt')
literal=read(L/'inputs/literal382297.json')
save(L/'reservation.json',dict(ids=[382297],rows=[literal],purpose='Second adversarial qualification of the transitive-tournament bunkbed proof; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
tt=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in tt.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
assert 'Campaign57/60' in common;common=common.replace('Campaign57/60','Campaign57/80')
detail='''TARGET: second adversarial qualification of MathDB 382297, the bunkbed conjecture BBC(E7,T_n) for transitive tournaments (Hollom, arXiv:2406.01790, Model 4.5 and Conjecture 6.4). An author proof is in inputs/author-CANDIDATE.md. The first review, inputs/review-r1-REVIEW.md, passed exact scope and the full ordinary mathematics, and gave a qualified bounded pass on prior art and significance. In this campaign five candidates were later excluded when a deeper check found a generic route or a complete source reduction, including one that had first been recommended as creditable. Your job is to try hard to do the same here, and to report honestly if you cannot.

READ FIRST. inherited-denials.json is over 280 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges. Save every native search response in the very next tool call after it returns, before any other step.

YOUR OWN SUPPLIED INPUTS ARE PERMITTED even though the campaign's general protection covers bunkbed material: everything under inputs/ in your own lane. Do not access any other bunkbed lane or integration.

PROOF. Read inputs/author-CANDIDATE.md critically and check each step. For this second review that satisfies the reconstruction requirement in the common text. Report any error, but do not re-derive what is already paid. The Lean definitions are in inputs/lean-definitions-BunkbedBase.lean: check that they say exactly what the source says, including the single bidirectional vertical token and the v=u convention.

CLOSED WORK, NO RECOVERY BY ANY ROUTE. The Przybylowski final journal version, DOI 10.1016/j.ejc.2025.104289, is closed to all new deliveries, as is everything in inherited-denials.json. Supplied copies under inputs/sources may be read. Before every GET, consider whether the host might redirect to a blocked route; a rejected redirect ends your network work, so prefer direct arXiv or open institutional PDFs you actually observed. Do not use Citeseer or Wayback.

THE ADVERSARIAL QUESTIONS. Answer each concretely:
1. Try to write the shortest possible proof, and say how long it is. Attempt a direct injection or measure-preserving coupling; conditioning on the vertical tokens and reflecting at the first or last use of one; and adapting the complete-graph arguments in inputs/sources/bunkbed-complete-correct.txt and inputs/sources/bunkbed-leander.txt. If a few lines suffice, or the known techniques transfer with only routine changes, say so and give the bridge, because that would make the existing proof routine.
2. Say exactly where transitivity is used. Does the same argument prove the statement for a broader class, such as all transitive acyclic digraphs of some type, interval orders, or graphs where every later vertex sees a nested set? Printed work shows the statement fails for general acyclic digraphs (inputs/sources/bunkbed-acyclic.txt), so identify what separates T_n from those counterexamples. If T_n is a parameter instance of a law with the same proof, say so.
3. Establish what the source and the thesis (inputs/sources/bunkbed-thesis.txt) say about this case. Is it presented as genuinely open and hard, as an easy afterthought, or with a suggested method? Decide whether a specialist would regard resolving it as new information.
4. Search later literature, 2024 to 2026, for proofs or disproofs in E7 or D7 or for tournaments and transitive or acyclic families, reading any applicable body through a permitted URL. A bounded nonmatch is not a worldwide novelty claim.
5. Spot-check the family comparison against accepted scopes rather than repeating it, focusing on any percolation, reachability or reflection result.
If you find an applicable theorem or a complete routine reduction, recommend exclusion and give the bridge. If you cannot after a real attempt, say so and say what the bounded search did and did not cover.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, routine adaptations, wording, domain or endpoint corrections, known results and parameter instances, and shortness alone is not an exclusion. Give the strongest case on each side. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR CORRECTION, with reasons. Root alone adjudicates.

FORMAL. Do not run Lean. A separate lane is working toward the endpoint; do not access it.

Author proposal and first review are not acceptance. Credit 0; campaign 57/80 unchanged.
'''
peers=['expanded-corpus-r526','transitive-bunkbed-reach-formal-deepseek-r20'];task=common.format(lane=L,id=382297,peers=', '.join(peers))+'\nTARGET-SPECIFIC SECOND QUALIFICATION\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+[q for q in (L/'inputs').rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
rdy=dict(utc=now,lane=str(L),mathdb_id=382297,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,target_new=80,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'bunkbed-qualification-r2-ready.json',rdy);save(ROOT/'selection-routing-bunkbed-qualification-r2.json',dict(ids=[382297],sources=[literal['source_url']],lane=str(L),task_sha256=rdy['task_sha256'],metadata_only=True))
print(json.dumps(dict(r525_manifest=212,frozen=13,corpus=20,history=919,next=rdy,credit=0,accepted_new=57)))
