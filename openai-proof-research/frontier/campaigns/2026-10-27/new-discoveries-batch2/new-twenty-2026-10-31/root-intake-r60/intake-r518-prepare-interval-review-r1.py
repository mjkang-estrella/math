"""Root documentary verification of r518 and preparation of an independent 336276 review, with 341690 queued; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r518';L=P/'interval-kwidth-limit-source-review-sol-r1';assert not L.exists()

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==245 and m['qualified_survivors']==0 and m['frozen_after_count']==13
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=sorted(m['terminal_exclusions']);assert set(aex)=={'MANIFEST.json','SEAL.json','seal_manifest.receipt.json','seal_manifest.output.txt'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{'get_istrate.receipt.json':1})
route=read(ROOT/'selection-routing-r518.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');assert len(ids)==len(gates)==20 and set(ids)==set(map(int,gates))
sources={};bound={}
for key in map(str,ids):
 v=read(A/'originals'/f'{key}-provenance.json');raw,obj,token=corpus(v);assert (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj['mathdb_id']==int(key)
 assert token.decode()==v['statement_token'] and dg(obj['statement'].encode())==v['statement_sha256'] and (A/'originals'/f'{key}-statement-token.txt').read_text().strip()==token.decode() and gates[key]['literal_statement']==obj['statement'];sources[key]=obj['source_url'];bound[key]=(raw,obj,v)
assert collections.Counter(v['disposition'] for v in gates.values())=={'PARK_EXACT_GAP_OR_UNAUTHENTICATED_PUBLIC_LEAD':18,'AUTHOR_FULL_ORDINARY_PROPOSAL_SCIENTIFIC_HOLD':2} and all(str(v['credit'])=='0' and v['qualified_survivor'] is False and v['accepted'] is False for v in gates.values())
assert {k for k,v in gates.items() if v['disposition'].startswith('AUTHOR')}=={'341690','336276'}
abudget=search(A,3,9,3,9,['search1-response.json','search2-response.json','search3-response.json'])
ae=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=9,success=5,redirect=3,unavailable=1),3)
un=next(e for e in ae if e['event']=='unavailable');assert un['url']=='https://tcs.ieat.ro/members/gistrate/' and un['status']==500
wr=[e for e in ae if e['event']=='attempt' and ('1742-5468' in e['url'] or 'perfdrive' in e['url'])];assert len(wr)==3
hard=(A/'sources/interval.pdf').read_bytes()==(A/'sources/interval-final.pdf').read_bytes();assert hard
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==len(allow)==896 and {x['path'] for x in history}==set(allow)
for x in history:
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482,519]) and 'formal' not in x['path'].rsplit('/',1)[-1].lower()
 if x.get('sha256'):assert allow[x['path']]==x['sha256'],x['path']

ass='r518 zero qualified survivors, two author-complete ordinary proposals, neither independently reviewed. 336276: for every fixed k>=2 the expected k-width of a sequence of n random intervals divided by n tends to 1/(k+1), by an exact Hall deficiency identity, a threshold lower bound, and a consecutive-time-block suffix-maxima upper bound that telescopes uniformly over every cut, finished with an elementary empirical-CDF mesh estimate. 341690: exact one-versus-three TISGM count for the ferromagnetic hard-core and soft-core Widom-Rowlinson model on Cayley trees for all k>=4, by a ratio parametrization and strict convexity of b*coth(bs), including the region the source left open. Independent proof, fidelity, significance, prior, family, formal, paper and acceptance gates unpaid. Other eighteen assigned original bodies unread; recorded parks are not open-status or public-proof certifications. 347305, 340819 and 332314 have source-own results; 337435 and 344405 are body-unread leads. Verified 245 manifest files, 20 corpus bindings, 13 frozen, 896 saved history entries, 9 charged GET hops (5 transport successes including 3 PDF responses, 3 redirects, 1 HTTP 500), 3 searches / 9 strings with responses saved. The interval source and publisher PDFs are byte-identical. The WR final returned a Radware verification page and that entire work is now closed. No formal dispatch or credit.'
work='Kissel, Kuelske and Rozikov, Hard-core and soft-core Widom-Rowlinson models on Cayley trees, arXiv 1901.09258 all versions and JSTAT 2019 043204 DOI 10.1088/1742-5468/ab081e'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after the DOI chain delivered a Radware verification page and no article; no script, form, cookie or retry. Pre-denial cached v1 and metadata stay readable and are not final-equivalence evidence.'
gs='Exact metadata page https://tcs.ieat.ro/members/gistrate/ unavailable after HTTP 500, including all alternate deliveries of that page. This is NOT a denial of any distinct Istrate paper.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),seal_sha256=sha(A/'SEAL.json'),task_reservation_genesis_verified=True,verified_manifest_files=245,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,new_unavailable=read(A/'NEW-UNAVAILABLE.json'),verified_saved_history_names=896,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS_TWO_AUTHOR_PROPOSALS_336276_ROUTED_341690_QUEUED',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r539.json');den['utc']=now;den['root_r518_scope']=ass;den['root_wr341690_final_closure']=fs;den['root_istrate_author_page_closure']=gs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{e['url_key'] for e in wr}|{un['url_key'],'arxiv.org/abs/1901.09258','arxiv.org/pdf/1901.09258'});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'1901.09258','10.1088/1742-5468/ab081e'})
den['records'].append(dict(url=wr[0]['url'],reason=dict(status=200,artifact=work,restriction=fs),evidence=dict(path=str(A/'NEW-UNAVAILABLE.json'),sha256=sha(A/'NEW-UNAVAILABLE.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
den['records'].append(dict(url=un['url'],reason=dict(status=500,artifact='Gabriel Istrate official author page',restriction=gs),evidence=dict(path=str(A/'NEW-UNAVAILABLE.json'),sha256=sha(A/'NEW-UNAVAILABLE.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
save(P/'expanded-corpus-r518-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r540.json';save(denpath,den)

L.mkdir();(L/'inputs').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
raw,literal,binding=bound['336276'];(L/'inputs/original336276.raw.jsonl').write_bytes(raw);save(L/'inputs/literal336276.json',literal);save(L/'inputs/provenance336276.json',binding);save(L/'inputs/author-gates336276.json',gates['336276'])
for f in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','ACTUALBRIEF.md','NEW-UNAVAILABLE.json','access-inventory.json','search1-response.json','search2-response.json','search3-response.json','get-interval.json','get-interval-final.json','get-istrate.json']:shutil.copyfile(A/f,L/'inputs'/f)
for f in ['interval.pdf','interval.txt','interval-final.pdf']:shutil.copyfile(A/'sources'/f,L/'inputs'/f)
shutil.copyfile(ROOT/'accepted57-review-context.json',L/'inputs/accepted57-scopes.json')
prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,L/'inputs/prior39-scopes.json')
save(L/'reservation.json',dict(ids=[336276],rows=[literal],purpose='Independent ordinary proof, literal/source, prior-art and significance review of the random-interval k-width limit proposal; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
t=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in t.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''TARGET: MathDB 336276, the random-interval sequence k-width scaling conjecture. Primary source: Balogh, Bonchis, Dinis, Istrate and Todinca, On the heapability of finite partial orders, arXiv 1706.01230, supplied as inputs/interval.pdf; inputs/interval-final.pdf is the byte-identical publisher PDF of DMTCS 22(2020)1 paper 17. interval.txt is extraction only. The original raw record is inputs/original336276.raw.jsonl.

READ FIRST. inherited-denials.json is about 245 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges. Save every native search response in the very next tool call after it returns, before any other step.

The author FULLCANDIDATE.md is an unreviewed proposal and also contains the unrelated 341690; ignore that part. Root has verified provenance only, with a hand spot check of inequality (D) and the telescoping that does not replace yours. Disclosed mechanism: an exact Hall-deficiency identity for the minimum number of chronological k-ary heapable classes, a lower bound from one threshold cut, an upper bound uniform over every Hall cut from consecutive time blocks and suffix maxima that telescopes, and a mesh bound for empirical CDFs. Reconstruct the proof or a precise GAP yourself before opening FULLCANDIDATE.md or DORMANT-SOL-FORMAL-PLAN.md.

PRIORITY ONE: THE MODEL. The literal says the conjecture contrasts with the known behaviour for k=1, and the author reports that the source's k=1 square-root statement conflicts with the model the proposal uses, under which k=1 would also be linear with constant 1/2. That is the strongest sign the random model or the definition of k-width may have been misread, so settle it before anything else, from the actual glyphs. Determine exactly how the n random intervals are generated and in what order they arrive; the definition of the partial order on intervals and whether its inequalities are strict; the definition of a k-heapable sequence and of k-width for a sequence, including whether parents must precede children in time, whether classes are trees or forests, and whether the k=1 case in the source is the same statistic as k>=2. Explain exactly what the source says about k=1 and whether it is a source error, a different statistic, or evidence against the proposal. Any model mismatch is fatal to the proposal and must be reported as such.

LITERAL AND SOURCE BINDING. Compare the MathDB literal word for word with Conjecture 1 on p21 and any neighbouring statement. Check whether the existence of c_k and the value 1/(k+1) are both asserted, and for exactly which k. Render and view the pages carrying the definitions and the conjecture.

ORDINARY AUDIT. Check at least: the matching-to-forest correspondence in both directions, including supply copies, roots, and acyclicity from strict time order; the exact deficiency formula and its proof with k-fold neighbour counting; the marginal CDFs of L and R; the optimization giving 1/(k+1); inequality (D), including that the counted parents in different blocks are distinct neighbours and the role of the later-block buffer; the replacement of N_q by a and its error; the telescoping and the bound on it; the dependence of the suffix maxima on S and why the sup-norm control handles it; the expected supremum mesh bound; the order of the limits in n, h and m; small n relative to m; ties and null events; and measurability.

PRIOR ART. The strongest specific item is Language (and Series) of Hammersley-Type Processes, which reportedly repeats a related Conjecture 20 and whose body is unread; identify it through search and read it within budget if a real permitted URL is observed. The official author page https://tcs.ieat.ro/members/gistrate/ is closed; distinct Istrate papers are not. Also search for later work on heapability of random intervals, online or chronological b-matching limits and any proof of this conjecture. A bounded nonmatch is not a worldwide novelty claim.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, routine adaptations and known results, and shortness alone is not an exclusion. Give the strongest case on each side. Negative: this may be a routine law-of-large-numbers argument for a bipartite matching with a monotone structure, possibly subsumed by random ordered b-matching or stochastic allocation results; if so, give the actual primary theorem and the complete bridge. Positive: the source states this as an open conjecture supported only by experiments, its matching theorem does not give the limit, and the temporal block envelope is a new global step over arbitrary time-dependent cuts. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE, with reasons. Root alone adjudicates.

FAMILY AND FORMAL. Compare against all supplied 57+39 scopes. Do not run Lean. Record which formal infrastructure is unpaid, including the product uniform measure on endpoints, the definition of k-width, Hall deficiency, expectation of a finite maximum and the limit, and give a realistic feasibility estimate, noting that heavy measure-theory imports are currently hard to kernel-check here. Write a dormant Sol formal brief only if the scientific gates prospectively survive.

Author proposal is not an independent PASS. Credit 0; campaign 57/60 unchanged.
'''
peers=['high-girth-ur-matching-formal-sol-r8','expanded-corpus-r519'];task=common.format(lane=L,id=336276,peers=', '.join(peers))+'\nTARGET-SPECIFIC INDEPENDENT REVIEW\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+list((L/'inputs').iterdir());save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=336276,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'interval-kwidth-review-r1-ready.json',ready);save(ROOT/'selection-routing-interval-kwidth-review-r1.json',dict(ids=[336276],sources=[literal['source_url']],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
save(ROOT/'r518-intake-report.json',dict(utc=now,files=245,frozen=13,corpus_bindings=20,history_names=896,review_ready=ready,queued_for_review=[341690],credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r518_manifest=245,frozen=13,corpus=20,history=896,review=ready,queued=[341690],credit=0,accepted_new=57)))
