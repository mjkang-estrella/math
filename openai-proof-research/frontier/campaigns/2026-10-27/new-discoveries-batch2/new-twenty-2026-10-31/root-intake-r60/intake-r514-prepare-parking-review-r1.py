"""Root documentary verification of r514 and preparation of an independent 323531 review; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r514';L=P/'parking-strong-a2-source-review-sol-r1';assert not L.exists()

def manifest_map(a,name,count,terminal,exfield):
 m=read(a/name);assert len(m['files'])==count and m['credit']==0
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
 return ex

# Every documentary check precedes any root mutation.
aex=manifest_map(A,'SHA256-MANIFEST.json',157,'seal_manifest','terminal_non_circular_self_exclusions');frozen(A,13);arec=receipts(A,{'get_parking_author.receipt.json':1})
route=read(ROOT/'selection-routing-r514.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'corpus-provenance.json');assert len(ids)==len(prov)==len(gates)==20 and set(ids)==set(map(int,gates))=={v['id'] for v in prov}
sources={}
for v in prov:
 key=str(v['id']);raw,obj,token=corpus(v)
 assert (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj==v['object'] and obj['mathdb_id']==v['id']
 assert token.decode()==v['raw_statement_token'] and dg(token)==v['raw_statement_token_sha256'] and dg(obj['statement'].encode())==v['decoded_statement_utf8_sha256']
 assert gates[key]['literal_statement']==obj['statement'];sources[key]=obj['source_url']
assert all(str(v['accepted_credit'])=='0' and not v.get('qualified_survivor') for v in gates.values())
abudget=search(A,3,9,3,9,['search1-response.json','search2-response.json','search3-response.json'])
ae=guard(A,list(A.glob('get-*-plan.json')),ids,dict(attempt=7,success=6,unavailable=1),5)
failure=next(e for e in ae if e['event']=='unavailable');assert failure['url']=='https://mathweb.ucsd.edu/~bprhoades/fpark.pdf' and failure['status'] is None and 'CERTIFICATE_VERIFY_FAILED' in failure['error']
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==len(allow)==885 and {x['path'] for x in history}==set(allow)
for x in history:
 rel=Path(x['path']).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482,513]) and 'high-girth-ur-matching-formal' not in x['path'] and allow[x['path']]==x['sha256']

ass='r514 zero qualified survivors. 323531: author-complete negation of the cached literal Strong Conjecture via an explicit A2, k=3, degree 10 equivariant hsop with 46 fixed points instead of 100; independent proof review, source reconciliation, prior art, significance, family, formal, paper and acceptance gates all unpaid. Apparent Proposition 4.4 restriction-to-ambient error and the contrary Table 1 A2 all-k claim in companion 1504.06869 need reconciliation. 337260 proposed upper-half proof only, lower half unpaid, no helper credit. 338136 routes sustained, cut-preserving balanced-exchange lemma unpaid. 378927 exact public source-owned correction, excluded. Other sixteen assigned original bodies unread; recorded statuses are not open-status certifications. Verified 157 manifest files, 20 corpus bindings, 13 frozen, 885 saved history names, 7 charged GET hops (6 successes: 5 PDF, 1 HTML; 1 TLS failure), 3 searches / 9 strings. No formal dispatch or credit.'
work='Brendon Rhoades Parking Structures Fuss Analogs arXiv 1205.4293 all versions and J. Algebraic Combinatorics 40(2) (2014) 417-473 final'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after the author-host TLS certificate verification failure; no retry, TLS bypass, identity correction or alternate recovery. Pre-denial cached v2 and metadata are documentary only, not final-equivalence evidence. Distinct companion 1504.06869 is not this work.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'SHA256-MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=157,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,new_unavailable=read(A/'NEW-UNAVAILABLE.json'),verified_saved_history_names=885,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS_ONE_AUTHOR_NEGATION_ROUTED_TO_INDEPENDENT_REVIEW',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r527.json');den['utc']=now;den['root_r514_scope']=ass;den['root_parking323531_final_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{failure['url_key'],'arxiv.org/abs/1205.4293','arxiv.org/pdf/1205.4293'});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'1205.4293'})
den['records'].append(dict(url=failure['url'],reason=dict(status=None,error=failure['error'],artifact=work,restriction=fs),evidence=dict(path=str(A/'NEW-UNAVAILABLE.json'),sha256=sha(A/'NEW-UNAVAILABLE.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
save(P/'expanded-corpus-r514-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r528.json';save(denpath,den)

L.mkdir();(L/'inputs').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
raw=(A/'originals/323531.jsonl').read_bytes();literal=json.loads(raw);(L/'inputs/original323531.raw.jsonl').write_bytes(raw);save(L/'inputs/literal323531.json',literal);save(L/'inputs/provenance323531.json',next(v for v in prov if v['id']==323531));save(L/'inputs/author-gates323531.json',gates['323531'])
for f in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','ACTUALBRIEF.md','NEW-UNAVAILABLE.json','source-read-inventory.json','http-search-inventory.json','history-matches.json','search1-response.json','search2-response.json','search3-response.json','get-parking-plan.json','get-parking-metadata-plan.json','get-parking-author-plan.json','get-evidence-plan.json']:shutil.copyfile(A/f,L/'inputs'/f)
for f in ['parking.pdf','parking.txt','parking-metadata.html','parking-page17.jpg','parking-page20.jpg','parking-page22.jpg','evidence.pdf','evidence.txt','evidence-page4.jpg']:shutil.copyfile(A/'sources'/f,L/'inputs'/f)
shutil.copyfile(ROOT/'accepted57-review-context.json',L/'inputs/accepted57-scopes.json')
prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,L/'inputs/prior39-scopes.json')
save(L/'reservation.json',dict(ids=[323531],rows=[literal],purpose='Independent ordinary counterexample, literal/source, prior-art and significance review of the parking-space Strong Conjecture negation; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
t=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in t.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''TARGET: MathDB 323531, the Strong Conjecture for algebraic and noncrossing parking spaces. Primary source: arXiv 1205.4293v2, supplied as inputs/parking.pdf (parking.txt is extraction only; the page JPEGs are the author's renders). Distinct companion: arXiv 1504.06869v2, Evidence for parking conjectures, supplied as inputs/evidence.pdf. The original raw record is inputs/original323531.raw.jsonl.

The author FULLCANDIDATE.md is an unreviewed proposal. Root has verified provenance only. Disclosed witness: W=A2 (rank 2, h=3), k=3, degree 10. On the complexified reflection representation with coordinates x,y, c.x=zeta x, c.y=zeta^(-1) y, s.x=y, s.y=x, take theta1=(x^10+3 x^4 y^6)/4 and theta2=(y^10+3 x^6 y^4)/4. The claim is that this is an equivariant hsop whose fixed locus has 46 points rather than 100. Verify it yourself by hand, and reach a proof or precise GAP, before opening FULLCANDIDATE.md or DORMANT-SOL-FORMAL-PLAN.md.

LITERAL AND SOURCE BINDING. Settle each from the actual glyphs, not from the author's summary:
1. Compare the MathDB literal word for word with the Strong Conjecture printed in v2. Determine the real quantifier: every equivariant hsop, some hsop, a specific or Cherednik-produced hsop. Keep the Weak, Intermediate, Strong and Generic Strong statements separate.
2. Read the definitions of hsop, carrying V*, V^Theta, multiplicity and the coordinates or basis allowed. Decide whether the x_i may be the complex coordinates x,y used by the witness or must be real or otherwise restricted, and how a change of basis acts. Confirm the witness meets every standing hypothesis, including real reflection group, rank, Coxeter number, the range of k and any coprimality, reality or genericity assumption printed anywhere.
3. The literal is a conjunction: distinct points of multiplicity one, an identification with Park^alg, and a bijection with Park^NC. The witness addresses only the first conjunct. State whether that refutes the whole statement and how an exact endpoint should bind it.

ORDINARY AUDIT. Check at least: homogeneity, weights and equivariance on generators and their extension to W; linear independence; the common zero locus over all of C^2; the factorization y theta1 - x theta2 = xy(x^3-y^3)^3/4; exhaustiveness and disjointness of the origin, axis and ratio-line cases; the exact count, noting that an upper bound below 100 suffices. As an internal consistency test only, compare the local multiplicities at the 46 points with the Bezout total of 100, and say whether they add up. Check the Jacobian claim at (1,1).

SOURCE CONFLICTS TO RECONCILE.
- Proposition 4.4 and its proof, pp. 20-22 of v2: decide whether the restriction-to-a-flat step really fails to give ambient simplicity, and whether the proposition is inconsistent with the witness.
- Table 1 on p. 2 of 1504.06869v2 reportedly prints Strong for A2 at all k. Read exactly what is claimed, under which definition of Strong, and what proof or citation supports it. If its definitions exclude the witness, say which clause does. If there is a real contradiction, say so precisely and do not assume which side is right.
- Establish whether either paper indicates the authors knew or expected non-generic failure, given that a Generic Strong Conjecture was separately formulated.

SOURCE CLOSURE. The entire work 1205.4293, all versions, and its 2014 J. Algebraic Combinatorics final are closed for all new deliveries after a TLS failure on the author-hosted copy; see NEW-UNAVAILABLE.json and inherited-denials.json. Do not retry or recover it by any route. The cached v2 is a pre-denial copy, not evidence of final equivalence, so record a source-final HOLD and assess how much that HOLD matters given the MathDB literal. 1504.06869 and its final version are distinct works and may be requested within budget if a real URL is observed. Run a bounded search for later work on non-reduced or non-generic hsop fixed loci in parking spaces and for any published correction or counterexample. A bounded nonmatch is not a worldwide novelty claim.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, wording, domain or endpoint corrections, parameter instances and known results, and shortness alone is not an exclusion. Give the strongest case on each side. Negative: the universal hsop quantifier may be an overstatement that the separately formulated Generic Strong Conjecture already repairs, so a special non-generic parameter could be a standard discriminant collision that only corrects the quantifier. Positive: the printed conjecture deliberately quantifies over all equivariant hsops, the witness is in the smallest nontrivial type at an interior k, the companion calls reducedness the outstanding algebraic obstacle, and a confirmed conflict with Proposition 4.4 or Table 1 would be substantive. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR CORRECTION, with reasons. Root alone adjudicates.

FAMILY AND FORMAL. Compare against all supplied 57+39 scopes. Do not run Lean. Record which formal bindings are unpaid, including the real reflection group and Coxeter number for A2, hsop and equivariance, the fixed-locus root bound, and how the Park conjuncts are stated, and give a realistic feasibility estimate. Write a dormant Sol formal brief only if the scientific gates prospectively survive.

Author proposal is not an independent PASS. Credit 0; campaign 57/60 unchanged.
'''
peers=['high-girth-ur-matching-formal-sol-r4','nfm-dirichlet-psd-source-review-sol-r1'];task=common.format(lane=L,id=323531,peers=', '.join(peers))+'\nTARGET-SPECIFIC INDEPENDENT REVIEW\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+list((L/'inputs').iterdir());save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=323531,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'parking-strong-a2-review-r1-ready.json',ready);save(ROOT/'selection-routing-parking-strong-a2-review-r1.json',dict(ids=[323531],sources=[literal['source_url']],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
save(ROOT/'r514-intake-report.json',dict(utc=now,files=157,frozen=13,corpus_bindings=20,history_names=885,new_denial=failure['url'],review_ready=ready,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r514_manifest=157,frozen=13,corpus=20,history=885,new_denial=failure['url'],review=ready,credit=0,accepted_new=57)))
