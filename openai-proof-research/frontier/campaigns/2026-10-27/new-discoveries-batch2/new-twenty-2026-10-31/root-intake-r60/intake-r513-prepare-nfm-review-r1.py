"""Root documentary verification of r513 and preparation of an independent 352259 review; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r513';L=P/'nfm-dirichlet-psd-source-review-sol-r1';assert not L.exists()

def manifest_map(a,name,count,terminal,exfield):
 m=read(a/name);assert len(m['files'])==count==m['count']
 names=set()
 for n,x in m['files'].items():
  assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
  q=a/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
 ex=m[exfield];assert set(ex)=={name,terminal+'.receipt.json',terminal+'.output.txt'}
 inventory=set()
 for q in a.rglob('*'):
  assert not q.is_symlink()
  if q.is_file():inventory.add(str(q.relative_to(a)))
 assert inventory==names|set(ex)
 assert m['qualified_survivors']==0 and m['accepted_credit']==0
 return ex

# Every documentary check precedes any root mutation.
aex=manifest_map(A,'MANIFEST.json',143,'manifest_terminal','terminal_noncircular_self_exclusions');frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r513.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'provenance.json');assert len(ids)==len(prov)==len(gates)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
sources={}
for key,v in prov.items():
 raw,obj,token=corpus(v)
 assert (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj['mathdb_id']==int(key)
 assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and obj['statement']==v['statement'] and dg(obj['statement'].encode())==v['statement_utf8_sha256']
 assert gates[key]['record']['statement']==obj['statement'];sources[key]=obj['source_url']
assert not any(v['qualified_survivor'] for v in gates.values())
abudget=search(A,3,9,3,9,['search1-response.json','search2-response.json','search3-response.json'])
ae=guard(A,list(A.glob('get-*-plan.json')),ids,dict(attempt=6,success=6),5)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');skipped=read(A/'history-skipped.json')
assert len(history)==883 and len(allow)==885 and len(skipped)==2 and {x['path'] for x in history}|set(skipped)==set(allow)
for x in history:
 rel=Path(x['path']).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482,514]) and 'high-girth-ur-matching-formal' not in x['path'] and allow[x['path']]==x['sha256']

ass='r513 zero qualified survivors. 352259: author-complete ordinary proposal for NFM Conjecture 3.5 (arXiv 2110.08385v1); independent proof review, significance, novelty, family, formal, paper and acceptance gates all unpaid. Literal "Theorem 2" versus v1 Theorem 3.4 numbering and the k=1 infinite-logit domain are flagged for adjudication. A same-topic Waterloo dissertation chapter appeared in search at a /server/api/ URL, was never requested, and its body is unread. 369624 scalar endpoint only, all-q bridge unpaid. 377198 mechanisms only, transitive all-sequence uniqueness unpaid. 360389 and 360867 have public source statements, zero. Remaining fifteen assigned bodies unread; their recorded gaps are not open-status certifications. Bowtie public counterclaim is navigation only, actual body HOLD. Verified 143 manifest files, 20 corpus bindings, 13 frozen, 883 saved history names (2 peer-filtered skips), 6 GET successes (5 PDF, 1 HTML), 3 searches / 9 strings, no new denial. Bootstrap and early documentary truncations retained by the author; no universal process clearance. No formal dispatch or credit.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=143,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=883,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS_ONE_AUTHOR_PROPOSAL_ROUTED_TO_INDEPENDENT_REVIEW',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r526.json');den['utc']=now;den['root_r513_scope']=ass
save(P/'expanded-corpus-r513-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r527.json';save(denpath,den)

L.mkdir();(L/'inputs').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
raw=(A/'originals/352259.jsonl').read_bytes();literal=json.loads(raw);(L/'inputs/original352259.raw.jsonl').write_bytes(raw);save(L/'inputs/literal352259.json',literal);save(L/'inputs/provenance352259.json',prov['352259']);save(L/'inputs/author-gates352259.json',gates['352259'])
for f in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','ORDINARY-DERIVATIONS.md','source-read-inventory.json','ACTUALBRIEF.md','search1-response.json','search2-response.json','search3-response.json','get-nfm-plan.json','get-nfm-meta-plan.json']:shutil.copyfile(A/f,L/'inputs'/f)
for f in ['nfm.pdf','nfm.txt','nfm-abs.html','nfm-page8.png','nfm-page9.png']:shutil.copyfile(A/'sources'/f,L/'inputs'/f)
shutil.copyfile(ROOT/'accepted57-review-context.json',L/'inputs/accepted57-scopes.json')
prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,L/'inputs/prior39-scopes.json')
save(L/'reservation.json',dict(ids=[352259],rows=[literal],purpose='Independent ordinary proof, literal/source, prior-art and significance review of the NFM Dirichlet conjecture proposal; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
t=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in t.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''TARGET: MathDB 352259, the NFM positive-semidefinite subgraph conjecture under Dirichlet noise. Primary source: Majmudar and Vavasis, Robust Correlation Clustering with Asymmetric Noise, arXiv 2110.08385v1, supplied as inputs/nfm.pdf (nfm.txt is extraction only). The original raw record is inputs/original352259.raw.jsonl.

The author FULLCANDIDATE.md is an unreviewed proposal. Root has verified provenance only. Disclosed mechanism: a fixed positive-mass cap of nodes with a large j-th coordinate supplies uniformly positive edges; a threshold t chosen close enough to 1/sqrt(2) makes every negative edge magnitude uniformly small; a second-moment bound on the iid cap count and a finite union bound finish. Reconstruct the proof or a precise GAP yourself before opening FULLCANDIDATE.md, ORDINARY-DERIVATIONS.md or DORMANT-SOL-FORMAL-PLAN.md.

LITERAL AND SOURCE BINDING. Settle each from the actual glyphs, not from the author's summary:
1. The MathDB literal says "the hypothesis of Theorem 2". v1 is reported to print the sufficient condition as Theorem 3.4 and the target as Conjecture 3.5. Determine whether they are the same statement and record exactly how an endpoint should bind this. A label mismatch earns no correction credit.
2. Read Definition 2.1 and all surrounding model text. Decide whether G is exactly a deterministic function of iid Dirichlet node vectors with W_uv = log(z_uv/(1-z_uv)) and zero diagonal, or whether there is any further edge sampling, sign randomness, noise, rounding, reweighting or normalization. Decide what "constant parameter alpha" means in the source (a vector fixed as n grows, or a symmetric vector with equal entries) and confirm the proof covers that meaning.
3. Read the complete hypothesis of Theorem 3.4, clause by clause: the definition of U; every requirement on S (nonempty, disjoint from U, positivity inside S, relation to the nodes outside S and U); the exact inequality, its sum range and its quantifiers. A witness meeting only part of the hypothesis does not pay the target.
4. Quantifiers: t may depend only on (k, alpha), not on j, n or the sample, and must lie strictly inside (1/2, 1/sqrt(2)). Keep the per-j "probability not converging to 0" separate from the proposal's stronger simultaneous statement. Choosing t near the endpoint in a way that depends on alpha is the pivot of the mechanism: check that the literal permits it, then separately assess whether it is what the conjecture means.
5. Domain: the literal does not exclude k=1, where the logit is infinite. Establish the source's standing range for k and recommend how root should bind it. Also check almost-sure finiteness of weights, null events and the meaning of n tending to infinity.

ORDINARY AUDIT. Check at least: positivity of the cap mass for every finite positive alpha including entries below 1 where the density is unbounded at the boundary; the bound z_uv >= theta^u_j theta^v_j; logit monotonicity; that S lies in V'_j and misses U_j because of positivity against every other selected node; the count of terms in the negative-mass bound; the order in which constants are chosen, all before n; empty U and empty S; strict inequalities; the second-moment constants and the union bound. If the proposal's PSD energy derivation is relied on anywhere, audit it as a separate gate; it is not the target.

SPECIFIC UNREAD PRIOR-ART ITEM. inputs/search2-response.json shows a result titled "Chapter 5 Robust Correlation Clustering with Asym..." at dspacemainprd01.lib.uwaterloo.ca under a /server/api/ bitstream URL, apparently a University of Waterloo dissertation containing this paper as a chapter. r513 never requested it. It might restate, resolve, amend or withdraw the conjecture. /server/api/ stays forbidden, and so does any request you know will redirect there. Within budget you may search for it and GET only a genuinely observed public non-API page such as a repository landing page. If the chapter cannot be read through a permitted delivery, record a specific HOLD naming this work; do not infer its content from the search excerpt. Also run a bounded check for a later or journal version of 2110.08385 and for later work citing this conjecture. A bounded nonmatch is not a worldwide novelty claim.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, endpoint or wording corrections, parameter instances and known results, and shortness alone is not an exclusion. Give the strongest case on each side. Negative: the source already supplies Theorem 3.4 and its Example 3.1 reportedly uses iid fringe counts with Hoeffding, so the proposal may be a short application in which letting t approach the interval endpoint trivializes the negative edges and exploits how the conjecture was phrased. Positive: it is a deliberate explicit conjecture across all (k, alpha), negative edges genuinely remain, and the authors left it open after experiments. Establish from the source what t values or uniformity the authors evidently intended, and whether the result delivers the PSD or recovery consequence they wanted. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE, with reasons. Root alone adjudicates.

FAMILY AND FORMAL. Compare against all supplied 57+39 scopes. Do not run Lean. Record which formal infrastructure is unpaid, including a Dirichlet measure on the simplex in the pinned mathlib, cap positivity, the iid product and the second-moment bound, and give a realistic feasibility estimate. Write a dormant Sol formal brief only if the scientific gates prospectively survive.

Author proposal is not an independent PASS. Credit 0; campaign 57/60 unchanged.
'''
peers=['high-girth-ur-matching-formal-sol-r4','expanded-corpus-r514'];task=common.format(lane=L,id=352259,peers=', '.join(peers))+'\nTARGET-SPECIFIC INDEPENDENT REVIEW\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+list((L/'inputs').iterdir());save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=352259,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'nfm-dirichlet-psd-review-r1-ready.json',ready);save(ROOT/'selection-routing-nfm-dirichlet-psd-review-r1.json',dict(ids=[352259],sources=[literal['source_url']],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
save(ROOT/'r513-intake-report.json',dict(utc=now,files=143,frozen=13,corpus_bindings=20,history_names=883,review_ready=ready,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r513_manifest=143,frozen=13,corpus=20,history=883,review=ready,credit=0,accepted_new=57)))
