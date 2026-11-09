"""Root documentary verification of the first 362896 review and preparation of a second focused qualification; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
V=P/'simplex-three-design-source-review-sol-r1';L=P/'simplex-three-design-primary-qualification-sol-r2';assert not L.exists()

# Every documentary check precedes any root mutation.
vex=manifest(V,'MANIFEST.json',124,'terminal_seal','self_exclusions');frozen(V,40);vrec=receipts(V,{'get_xu_primary.receipt.json':1})
ready=read(ROOT/'simplex-three-design-review-r1-ready.json');assert sha(V/'TASK.txt')==ready['task_sha256']
vbudget=search(V,2,6,2,6,['search-response-1.json','search-response-2.json']);ve=guard(V,[V/n for n in ['get-predecessor-metadata.json','get-predecessor-body.json','get-xu-primary.json']],[362896],dict(attempt=3,success=2,redirect=1,unavailable=1),1)
un=next(e for e in ve if e['event']=='unavailable');assert 'web.archive.org' in un['url'] and 'citeseerx' in un['url'] and read(V/'get_xu_primary.receipt.json')['exit']==1
review=read(V/'review.json');assert set(review)=={'362896'};g=review['362896'];assert g['recommendation']=='PARK' and g['credit']==0 and 'no gap found' in g['gates']['ordinary'] and g['gates']['family'].startswith('UNPAID')
for f in ['PROOF.md','REVIEW.md','NETWORK-STOP.md','NEW-UNAVAILABLE-REVIEW.json','source-map.json','inventories.json']:assert (V/f).is_file()

vs='362896 first independent review: full equal-weight ordinary proof reconstructed for every integer d>=3 including arbitrary real nodes, no ordinary gap found, retained as pre-stop ordinary evidence. Recommendation PARK because the review stopped early and did not finish its gates, not because a defect or prior proof was found. The printed nonexistence sentence matches Conjecture 7 and Definition 4 was viewed; visual Eq. 5 and Appendices B.1 and D are unpaid. Prior art unresolved: Fritsch 1970 closed and unread; a distinct Yuan Xu Transactions paper reached through a Citeseer link redirected to an inherited blocked Wayback route, the guard rejected it before dispatch, that work is closed and research stopped as required. The all-96 family comparison and the full correction read are unpaid. arXiv 1308.3188 is Cohn, Kumar and Minton, Optimal simplices and codes in projective spaces, not Baladram; that label was an error in the root brief, corrected here. Serious classical objection retained: n+1-node degree-three formulas are the classical minimal Gaussian-cubature regime and may subsume this even with free weights. ROOT DISPOSITION: ordinary support retained, no credit, no formal dispatch, second focused qualification authorized on existing campaign precedent. 124 manifest files, 40 frozen bindings verified.'
work='Yuan Xu Transactions minimal-cubature or orthogonal-polynomial paper identified only by Citeseer DOI fingerprint 8829c93a1b58e79af953c3f9880d02e74eafeba3, full bibliographic identity unread'
fs=f'Identified work {work}: all new deliveries unavailable after the Citeseer request redirected to an inherited blocked Wayback route and the guard rejected it before dispatch; no retry or alternate recovery. Its identity must not be guessed in order to recover it. Other distinct Xu papers and other cubature works are not blanket denied.'
vr=dict(utc=now,mathdb_id=362896,source_lane=str(V),manifest_sha256=sha(V/'MANIFEST.json'),verified_manifest_files=124,verified_frozen_bindings=40,verified_original_bindings=[362896],review=g,source_map=read(V/'source-map.json'),runner_receipts=vrec,guard_events=dict(collections.Counter(e['event'] for e in ve)),search_budget=vbudget,new_unavailable=read(V/'NEW-UNAVAILABLE-REVIEW.json'),scientific_summary=vs,reviewer_recommendation='PARK',root_disposition='ORDINARY_SUPPORT_RETAINED_REVIEW_STOPPED_EARLY_SECOND_QUALIFICATION_AUTHORIZED',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=vex,root_scope='Documentary integrity and root disposition only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r543.json');den['utc']=now;den['root_simplex362896_review_r1_scope']=vs;den['root_simplex_xu_citeseer_closure']=fs
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'8829c93a1b58e79af953c3f9880d02e74eafeba3'})
den['records'].append(dict(url='https://citeseerx.ist.psu.edu/document?doi=8829c93a1b58e79af953c3f9880d02e74eafeba3&repid=rep1&type=pdf',reason=dict(status=301,artifact=work,restriction=fs),evidence=dict(path=str(V/'NEW-UNAVAILABLE-REVIEW.json'),sha256=sha(V/'NEW-UNAVAILABLE-REVIEW.json'),guard_sha256=sha(V/'guard-ledger.jsonl'))))
save(P/'simplex-three-design-review-parent-integration-r1.json',vr);denpath=ROOT/'inherited-denials-r544.json';save(denpath,den)

L.mkdir();(L/'inputs').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(V/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
for q in sorted((V/'inputs').iterdir()):
 if q.is_file():shutil.copyfile(q,L/'inputs'/q.name)
for f in ['REVIEW.md','PROOF.md','review.json','source-map.json','NETWORK-STOP.md','NEW-UNAVAILABLE-REVIEW.json','search-response-1.json','search-response-2.json']:shutil.copyfile(V/f,L/'inputs'/('review-r1-'+f))
for f in ['predecessor.pdf','predecessor.txt','predecessor-metadata.html']:shutil.copyfile(V/'sources'/f,L/'inputs'/f)
literal=read(L/'inputs/literal362896.json')
save(L/'reservation.json',dict(ids=[362896],rows=[literal],purpose='Second focused qualification of the simplex 3-design nonexistence proposal: classical prior art, remaining source gates and family comparison; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
t=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in t.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''TARGET: second focused qualification of MathDB 362896, nonexistence of d-point simplex 3-designs. The first review, inputs/review-r1-REVIEW.md and inputs/review-r1-PROOF.md, reconstructed the full ordinary proof and found no gap, but stopped early when a fetch hit a blocked route. Your job is to finish the gates it could not, chiefly classical prior art.

READ FIRST. inherited-denials.json is over 250 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges. Save every native search response in the very next tool call after it returns, before any other step.

PROOF. Read inputs/review-r1-PROOF.md critically and check each step. For this second review that satisfies the reconstruction requirement in the common text. Do not spend effort re-deriving what it already pays, but report any error you find.

CORRECTION. The earlier brief wrongly called arXiv 1308.3188 a Baladram paper. It is Cohn, Kumar and Minton, Optimal simplices and codes in projective spaces. Do not substitute a different work under that identifier. Determine from the MathDB record and final-paper citations which paper is really the source's predecessor and whether it bears on this statement.

CLOSED WORKS, NO RECOVERY BY ANY ROUTE. Fritsch 1970 (Math. Comp. 24), and the Yuan Xu paper identified only by the Citeseer fingerprint in inherited-denials.json. Do not guess that Xu paper's identity in order to recover it, and do not request any Citeseer or Wayback URL. Distinct papers are not denied. Before every GET, consider whether the host is likely to redirect to a blocked route; a rejected redirect ends your network work, so prefer direct arXiv or open institutional PDF URLs that you actually observed.

PRIOR ART IS THE DECISIVE GATE. Classical cubature theory treats n+1-node degree-three formulas in n dimensions as the minimal Gaussian regime, with n=d-1. Answer these concretely:
1. Is nonexistence of (d)-node degree-three formulas on the (d-1)-simplex, with FREE weights, a known theorem? If so it immediately contains this equal-weight statement. Identify the actual primary or authoritative survey statement with its hypotheses, for example in the Mysovskikh, Stroud, Cools or Moeller tradition, reached through a permitted URL.
2. Independently of any source, decide how hard the free-weight case is using the classical common-zero or orthogonal-polynomial criterion, or by adapting this proof. If the free-weight statement follows quickly, say so, because that bears directly on whether this is routine. If free weights actually admit such a formula for some d, say so, because then the equal-weight restriction is doing real work.
3. Also check equal-weight Chebyshev-type cubature results and any existing simplex-design literature.
If you find an applicable theorem, give the complete bridge to the literal. A bounded nonmatch is not a worldwide novelty claim. If only closed works remain as specific applicable leads, record a precise HOLD naming them.

REMAINING SOURCE GATES. Render and view Eq. 5 on p5 and confirm the normalization and the meaning of the average. Read Appendix B.1 (the d=3 argument) and Appendix D (the fourth-moment rank bound), which the first review did not audit. Finish reading the supplied correction paper 2505.05894.

FAMILY GATE. Personally extract and compare all 57+39 supplied exact scopes, in small chunks so that nothing is truncated, and record each comparison. The first review left this unpaid.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, known results, parameter instances and corrections, and shortness alone is not an exclusion. Give the strongest case on each side, informed by your answers above. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR KNOWN, with reasons. Root alone adjudicates.

FORMAL. Do not run Lean. Separate the finite-sum algebra from the flat simplex measure and its moment formulas, note that heavy measure-theory imports are currently hard to kernel-check here, and write a dormant Sol formal brief only if the scientific gates prospectively survive.

Author proposal is not an independent acceptance. Credit 0; campaign 57/60 unchanged.
'''
peers=['interval-kwidth-formal-sol-r1','widom-rowlinson-tisgm-source-review-sol-r1'];task=common.format(lane=L,id=362896,peers=', '.join(peers))+'\nTARGET-SPECIFIC SECOND QUALIFICATION\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+list((L/'inputs').iterdir());save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
rdy=dict(utc=now,lane=str(L),mathdb_id=362896,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'simplex-three-design-qualification-r2-ready.json',rdy);save(ROOT/'selection-routing-simplex-three-design-qualification-r2.json',dict(ids=[362896],sources=[literal['source_url']],lane=str(L),task_sha256=rdy['task_sha256'],metadata_only=True))
print(json.dumps(dict(review_manifest=124,frozen=40,qualification=rdy,credit=0,accepted_new=57)))
