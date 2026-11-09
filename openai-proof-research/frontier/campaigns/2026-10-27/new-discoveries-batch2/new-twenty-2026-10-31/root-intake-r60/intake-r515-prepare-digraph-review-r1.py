"""Root documentary verification of r515 and preparation of an independent 350767 review; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r515';L=P/'digraph-aalpha-minimum-source-review-sol-r1';assert not L.exists()

# Every documentary check precedes any root mutation.
aex=manifest(A,'MANIFEST.json',126,'terminal_seal','terminal_noncircular_self_exclusions');frozen(A,13);arec=receipts(A,{'get_digraph_final.receipt.json':1})
aman=read(A/'MANIFEST.json');assert aman['credit']==0 and aman['no_other_exclusions'] is True
route=read(ROOT/'selection-routing-r515.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');bindings=read(A/'original-bindings.json');assert len(ids)==len(bindings)==len(gates)==20 and set(ids)==set(map(int,gates))
sources={};raws={}
for v in bindings:
 raw,obj,token=corpus(v);key=str(obj['mathdb_id']);assert key in gates and raw.decode()==v['raw'] and key not in raws
 assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and obj['statement']==v['statement_utf8'] and dg(obj['statement'].encode())==v['statement_utf8_sha256']
 assert gates[key]['literal_statement']==obj['statement'];sources[key]=obj['source_url'];raws[key]=(raw,obj,v)
assert all(str(v['credit'])=='0' and str(v['formal_dispatch'])=='False' and not v.get('qualified_survivor') for v in gates.values())
abudget=search(A,2,6,3,9,['search-response1.json','search-response2.json'])
ae=guard(A,[A/n for n in ['get-almost.json','get-digraph-final.json','get-digraph.json','get-psd.json']],ids,dict(attempt=5,success=3,redirect=2),3)
stop=[e for e in ae if e['event']=='attempt' and ('10.7153' in e['url'] or 'ele-math' in e['url'])];assert [e['url'] for e in stop]==['https://doi.org/10.7153/OAM-2022-16-67','https://oam.ele-math.com/16-67']
assert (A/'NETWORK-STOP.md').is_file() and read(A/'get_digraph_final.receipt.json')['exit']==1
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==888 and len(allow)==890
missing={p.rsplit('/',1)[-1] for p in set(allow)-{x['path'] for x in history}};assert missing=={'high-girth-ur-matching-primary-parent-integration-r2.json','high-girth-ur-matching-source-parent-integration-r1.json'}
for x in history:
 rel=Path(x['path']).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482]) and 'parking-strong-a2-formal' not in x['path'] and allow[x['path']]==x['sha256']

ass='r515 zero qualified survivors. 350767: author-complete ordinary proposal for the second, third and fourth minimum A_alpha spectral radius conjecture for strongly connected digraphs, all n>=5 and 0<=alpha<1, Xi-Wang 2105.10903v1 Conjecture 3.7; independent proof review, final-source, prior, novelty, significance, family, formal, paper and acceptance gates unpaid. Concrete routine-adaptation objection: the source structural reduction is reused and one scalar comparison is strengthened. 371594 three routes sustained, join classification gap unpaid. 365513 range correction with public intended theorem, zero. Other seventeen assigned original bodies unread; recorded gaps are not open-status certifications. Kuperberg exact public proof and principal-ratio leads are body-unread HOLDs. Network stopped after the final-source DOI redirected to HTTP, the guard rejected that target before dispatch and its logger failed; no HTTP fetch, retry or alternate delivery. Complete TASK and denials were personally read in chunks before network use. Verified 126 manifest files, 20 corpus bindings, 13 frozen, 888 saved history names, 5 charged HTTPS hops (3 PDF successes, 2 redirects), 2 searches / 6 strings. No formal dispatch or credit.'
work='Xi and Wang, On the A_alpha spectral radius of strongly connected digraphs, arXiv 2105.10903 all versions and Operators and Matrices final DOI 10.7153/OAM-2022-16-67'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after the DOI chain redirected to HTTP and the guard rejected it before dispatch; no HTTP request, HTTPS upgrade, retry or alternate recovery. The pre-failure cached 2105.10903v1 PDF stays readable and is not final-equivalence evidence. Distinct spectral papers are not blanket denied.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=126,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=888,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS_ONE_AUTHOR_PROPOSAL_ROUTED_TO_INDEPENDENT_REVIEW',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r532.json');den['utc']=now;den['root_r515_scope']=ass;den['root_digraph350767_final_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{e['url_key'] for e in stop}|{'doi.org/10.7153/oam-2022-16-67','arxiv.org/abs/2105.10903','arxiv.org/pdf/2105.10903'});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'2105.10903','10.7153/oam-2022-16-67'})
den['records'].append(dict(url=stop[0]['url'],reason=dict(status=None,artifact=work,restriction=fs),evidence=dict(path=str(A/'NETWORK-STOP.md'),sha256=sha(A/'NETWORK-STOP.md'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
save(P/'expanded-corpus-r515-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r533.json';save(denpath,den)

L.mkdir();(L/'inputs').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
raw,literal,binding=raws['350767'];(L/'inputs/original350767.raw.jsonl').write_bytes(raw);save(L/'inputs/literal350767.json',literal);save(L/'inputs/provenance350767.json',binding);save(L/'inputs/author-gates350767.json',gates['350767'])
for f in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','ORDINARY-ATTEMPTS.md','ACTUALBRIEF.md','NETWORK-STOP.md','READ-ACCESS-INVENTORY.json','search-response1.json','search-response2.json','get-digraph.json','get-digraph-final.json']:shutil.copyfile(A/f,L/'inputs'/f)
for f in ['digraph.pdf','digraph.txt']:shutil.copyfile(A/'sources'/f,L/'inputs'/f)
shutil.copyfile(ROOT/'accepted57-review-context.json',L/'inputs/accepted57-scopes.json')
prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,L/'inputs/prior39-scopes.json')
save(L/'reservation.json',dict(ids=[350767],rows=[literal],purpose='Independent ordinary proof, literal/source, prior-art and significance review of the digraph A_alpha minimum conjecture proposal; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
t=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in t.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''TARGET: MathDB 350767, the second, third and fourth minimum conjecture for the A_alpha spectral radius of strongly connected digraphs. Primary source: Xi and Wang, arXiv 2105.10903v1, supplied as inputs/digraph.pdf (digraph.txt is extraction only). The original raw record is inputs/original350767.raw.jsonl.

READ FIRST. inherited-denials.json is about 230 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges. A recent review made no searches or fetches because it never completed this read, so do it first; the prior-art check below needs your search budget.

The author FULLCANDIDATE.md is an unreviewed proposal. Root has verified provenance only, and made a spot check of equation (E) and the two-regime comparison that does not replace yours. Disclosed mechanism: Perron scalar equations for theta and infinity digraphs in the variables t=(lambda-alpha)/(1-alpha) and s=t-alpha/(1-alpha); a direct ordering of bicyclic digraphs; a shortest-cycle-plus-ear reduction; arc tables for the two exceptional spanning thetas; and an all-alpha comparison of the single-extra-arc graph G'_n with theta(0,2,n-4) from s^2 t^(n-2)=s+t+1, split at t=2. Reconstruct the proof or a precise GAP yourself before opening FULLCANDIDATE.md, ORDINARY-ATTEMPTS.md or DORMANT-SOL-FORMAL-PLAN.md.

LITERAL AND SOURCE BINDING. Settle each from the actual glyphs, not from the author's summary:
1. Compare the MathDB literal word for word with Conjecture 3.7 on p11 of v1: the range of n and alpha, which digraphs are second, third and fourth, and any uniqueness claim.
2. The author did NOT visually inspect figures or final glyphs. Render and view the pages defining theta(a,b,c), including any figure, and confirm the parameter convention, the direction of each path, and which digraphs the labels theta(0,1,n-3), theta(1,1,n-4), theta(0,2,n-4) really denote.
3. Determine exactly what the source already proves: the range of alpha in Theorem 3.4 and its companions, where its proof uses that range, and what remains for Conjecture 3.7.
4. Confirm the definitions: whether opposite arcs are allowed, simple, strongly connected, A_alpha using out-degrees, and spectral radius.

ORDINARY AUDIT. Check at least: the Perron facts used, including 1<lambda<max out-degree for noncycle graphs, s>0, s<=t, and strict monotonicity for proper subdigraphs when the matrix is padded by zero rows and columns and at alpha=0; the theta and infinity scalar equations and the direction of every root comparison, including uniqueness of the root of the monotone normalized equation; the bicyclic numerator ordering for n>=5 with its equality cases and exact isomorphism types; the claim that every noncycle strongly connected simple digraph contains a strongly connected bicyclic subdigraph through a shortest cycle and shortest ear, including length-two cycles from opposite arcs; every entry of both exceptional arc tables, exhaustively over all ordered pairs by hand (no enumeration program), at the short-chain boundaries n=5 with m=2 and m=1 and with empty index ranges. A_alpha uses OUT-degrees, so reversing a digraph is not automatically harmless. The proposal says the single-exception graphs are G'_n "or an isomorphic/reversed version with the same equations": verify each is genuinely isomorphic to G'_n or give its own equation. Check the elimination giving (E), the identity for q(t), both t regimes and n=5.

PRIOR ART AND SOURCE CLOSURE. The entire work 2105.10903 and its Operators and Matrices final, DOI 10.7153/OAM-2022-16-67, is closed for all new deliveries after the DOI chain redirected to HTTP; see NETWORK-STOP.md and inherited-denials.json. Do not retry or recover it by any route. The cached v1 is not evidence of final equivalence, so record a source-final HOLD and assess how much it matters given the MathDB literal. Run a bounded search for later work on the minimum A_alpha spectral radii of strongly connected digraphs and any proof of this conjecture, and read any genuinely applicable distinct primary source within budget. A bounded nonmatch is not a worldwide novelty claim.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, routine adaptations, parameter extensions and known results, and shortness alone is not an exclusion. Give the strongest case on each side. Negative: the source's structural reduction is reused and only one scalar comparison is strengthened, so this may be a routine extension of the source's own proof to the remaining alpha range. Identify precisely what fails in the source's argument beyond its range and how much of the proposal is genuinely new. Positive: this is a deliberate source conjecture settled over the full remaining real interval with exact unique minimizers and no change of scope. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE, with reasons. Root alone adjudicates.

FAMILY AND FORMAL. Compare against all supplied 57+39 scopes. Do not run Lean. Record which formal infrastructure is unpaid, in particular the irreducible nonnegative matrix and Perron facts for actual spectral radius, the explicit theta graphs and the exhaustive arc reduction, and give a realistic feasibility estimate. Write a dormant Sol formal brief only if the scientific gates prospectively survive.

Author proposal is not an independent PASS. Credit 0; campaign 57/60 unchanged.
'''
peers=['high-girth-ur-matching-formal-sol-r6','parking-strong-a2-formal-sol-r1'];task=common.format(lane=L,id=350767,peers=', '.join(peers))+'\nTARGET-SPECIFIC INDEPENDENT REVIEW\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+list((L/'inputs').iterdir());save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=350767,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'digraph-aalpha-minimum-review-r1-ready.json',ready);save(ROOT/'selection-routing-digraph-aalpha-minimum-review-r1.json',dict(ids=[350767],sources=[literal['source_url']],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
save(ROOT/'r515-intake-report.json',dict(utc=now,files=126,frozen=13,corpus_bindings=20,history_names=888,new_closure=work,review_ready=ready,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r515_manifest=126,frozen=13,corpus=20,history=888,review=ready,credit=0,accepted_new=57)))
