"""Documentary integrity/routing only; no root mathematical solving or Lean execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,base64
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
H=P/'high-girth-ur-matching-primary-qualification-sol-r2';J=P/'tensor-dominant-orbit-jaja-primary-sol-r3';A=P/'expanded-corpus-r511'
records={}
for key,lane,mname,count,fcount,terminal,exfield,readyfile,fail in [('highgirth',H,'MANIFEST.json',125,33,'seal-manifest','terminal_self_exclusions','high-girth-ur-matching-qualification-r2-ready.json',{'final-get.receipt.json':1}),('jaja',J,'MANIFEST.json',90,31,'seal_manifest','terminal_noncircular_self_exclusions','tensor-dominant-orbit-jaja-r3-ready.json',{'get_jaja_primary.receipt.json':1})]:
 ex=manifest(lane,mname,count,terminal,exfield);frozen(lane,fcount);rec=receipts(lane,fail)
 assert sha(lane/'TASK.txt')==read(ROOT/readyfile)['task_sha256'] and read(lane/(terminal+'.receipt.json'))['exit']==0
 mid=338806 if key=='highgirth' else 323694;v=read(lane/'inputs'/f'provenance{mid}.json');raw,obj,token=corpus(v)
 assert raw==(lane/'inputs'/f'original{mid}.raw.jsonl').read_bytes() and obj==read(lane/'inputs'/f'literal{mid}.json')==read(lane/'reservation.json')['rows'][0] and obj['mathdb_id']==mid
 if key=='highgirth':
  z=v['statement_tokens'][0];assert len(v['statement_tokens'])==1 and token.decode()==z['token'] and dg(token)==z['token_sha256'] and obj['statement']==z['decoded'] and dg(obj['statement'].encode())==z['decoded_sha256']
  budget=search(lane,1,2,2,6,['sources/search-one-full.json']);events=guard(lane,[q for q in (lane/'plans').glob('*.json') if 'url' in read(q)],[mid],dict(attempt=4,success=2,redirect=2),2)
  assert events[-1]['event']=='redirect' and events[-1]['location'].startswith('http://') and read(lane/'final-get.receipt.json')['exit']==1
  sm=read(lane/'source-map.json')[str(mid)]
  for label in ['thesis','goddard']:assert sha(lane/sm[label]['file'])==sm[label]['sha256']
 else:
  assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and dg(obj['statement'].encode())==v['statement_utf8_sha256']
  assert read(lane/'search-budget.json')==dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True)
  events=guard(lane,list((lane/'plans').glob('*.json')),[mid],dict(attempt=1,unavailable=1),0)
  assert events[-1]['status']==403
 records[key]=dict(utc=now,mathdb_id=mid,source_lane=str(lane),task_sha256=sha(lane/'TASK.txt'),manifest_sha256=sha(lane/mname),verified_manifest_files=count,verified_frozen_bindings=fcount,verified_original_bindings=[mid],review=read(lane/'review.json'),source_map=read(lane/'source-map.json'),runner_receipts=rec,guard_events=dict(collections.Counter(e['event'] for e in events)),credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary integrity/routing only; no root mathematical solving/programs/Lean/checkers.')

route=read(ROOT/'selection-routing-r511.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'SHA256-MANIFEST.json');assert len(m['files'])==120
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts and not (A/n).is_symlink() and sha(A/n)==x['sha256'] and (A/n).stat().st_size==x['bytes']
ex=m['exact_self_exclusions'];assert set(ex)=={'SHA256-MANIFEST.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(m['files'])|set(ex);frozen(A,13);rec=receipts(A,{'get_product_final.receipt.json':1});assert read(A/'terminal_manifest.receipt.json')['exit']==0
ids=read(A/'reservation.json')['ids'];prov=read(A/'original-provenance.json');gates=read(A/'results.json');assert len(ids)==20 and set(map(int,prov))==set(map(int,gates))==set(ids)
sources={}
for k,v in prov.items():
 raw,obj,token=corpus(v);mid=int(k)
 assert obj['mathdb_id']==mid and (A/'originals'/f'{mid}.jsonl').read_bytes()==raw and base64.b64decode(v['raw_base64'])==raw
 assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and obj['statement']==v['decoded_statement']==gates[k]['literal'] and dg(obj['statement'].encode())==v['decoded_sha256'];sources[k]=obj['source_url']
budget=search(A,2,6,3,9,['search-one-response.json','search-two-response.json']);events=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=5,success=4,unavailable=1),4);assert events[-1]['status']==403
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==875
for v in history:
 rel=Path(v['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in v['path'] for z in [395,463,466,482]) and v['path'] in allow and allow[v['path']]==v['sha256']
hs='338806 focusedreview retainedindependentordinary/v2literalPASS;actualFurst2019RestrictedMatchings COMPLETEChapter6/lowerproofs/Conj6.4 paid,allDelta intentionconfirmed,bibliographyandlaterrelevantdiscussionread;actualGoddard2005full13pagemanuscript/proofs boundednonmatches,URTheorem1attributionoriginal2001proofunread. No exactpublicrefutation/completeprimaryroutinebridgeauthenticated;strongall-gfixedDelta100positiveandconventionalexpander/URobjectionretained. FinalDOI10.1007/S00373-018-1991-8->HTTP302 guardrejectedBEFOREdispatch/loggerfailed,noHTTPfetch/no unavailablebackfill. ENTIRE original1803.11032/finalworkclosed,newdeliveriesforbidden,cachedoriginal/thesisnotfinalequivalence. Expert scientificHOLD preserved. ROOT authorizesUNCREDITEDFORMALRESEARCHseparately,NOTscientificPASS/acceptance/sourcewaiver.125manifestfiles33frozen1corpusbinding,4HTTPSGETcharged2PDF2redirect,1search2strings,28runnerreceiptsfailedfinalretained. No universalprocessclearance,read/truncation/native-transient-writerlimitsretained.'
js='323694 focusedlastnamedJaJa1979proofrequestreturned403beforebody;no retry,searchoralternate. EntireworkDOI10.1137/0208037/Optimal evaluation ofpairs ofbilinearforms closedtoALLnewdeliveries;actualJaJatheoremproofhypothesesunread,no priornonmatch/exclusionclaimed. Sumi3.3smallbinarysquarehelperattributionreadpredelivery,notcompleteall-p sourcebridge. OrdinaryPASSretained,currentofficialv1/nojournalboundedstatus(no specificfinalcounterclaim)notworldwideabsencecertificate. ROOT SCIENTIFIC_PARK,specificclosedpriorproof/routineobjectionunpaid,noformaldispatch.90manifestfiles31frozen1corpusbinding,1GET403/0success,0search,20runnerreceiptsfailed403retained;trustedprevious96nonmatchnotrepeated. ScientificHOLDretained,credit0.'
ars='r511 zeroqualifiedsurvivors.364140 AUTHOR all-m product-measure ordering-lawdimensionproposal:distinctletterwordalgebra,independentconjugatetangentdirectionsD=m+C(m),onenonzeroJacobianminorpositiveorthantpoint,normalizationALLsubsetmarginalfactorizationandranksubtractm =>lowerboundC(m),actualsourceTh5.13upperboundimported,notindependentlyPASS;assignedreview.361174/356297 sustainedroutesprecisegaps;17assignedoriginalbodiesunread.120manifestfiles20corpusbindings13frozen875savedhistorynamesverified;5GET4PDF1Wiley403,2search6strings. ENTIRE Models ofRandomSpanningTrees2407.20226/DOI10.1002/rsa.70063closedallnewdeliveries;predeliveryoriginal/13Mar2026authorcopynotfinalequivalence. ExistingR.Suck2002/accessibility-signatureprimaryleadunread,novelty/significance/family/formalunpaid. Task/source/history/denialpersonalreadtruncationqualificationsandunknownnative/transient/writerpeaksretained,nouniversalprocessPASS. No mathematicalprogram/Lean/child/publication/acceptance,credit0.'
records['highgirth'].update(scientific_summary=hs,root_disposition='ORDINARY_PASS_SCIENTIFIC_HOLD_UNCOUNTED_FORMAL_RESEARCH_SEPARATELY_AUTHORIZED')
records['jaja'].update(scientific_summary=js,root_disposition='SCIENTIFIC_PARK_SPECIFIC_CLOSED_JAJA_PROOF_UNPAID')
ar=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=120,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=rec,guard_events=dict(collections.Counter(e['event'] for e in events)),search_budget=budget,verified_saved_history_names=875,scientific_summary=ars,root_disposition='ZERO_QUALIFIED_SURVIVORS_364140_INDEPENDENT_REVIEW_ASSIGNED',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=ex)
den=read(ROOT/'inherited-denials-r523.json');den['utc']=now;den['root_highgirth338806_r2_scope']=hs;den['root_tensor323694_r3_scope']=js;den['root_r511_scope']=ars
closures=[('https://doi.org/10.1007/S00373-018-1991-8','Lower Bounds on the Uniquely Restricted Matching Number original1803.11032/final2019',read(H/'NETWORK-STOP.json')['338806']['new_work_closure'],H/'NETWORK-STOP.json',H/'guard-ledger.jsonl',{'doi.org/10.1007/s00373-018-1991-8','link.springer.com/10.1007/s00373-018-1991-8','arxiv.org/abs/1803.11032','arxiv.org/pdf/1803.11032'},'GuardHTTPredirectrejectedBEFOREdispatch;loggerfailure;no unavailableeventbackfill'),('https://epubs.siam.org/doi/abs/10.1137/0208037','JaJa1979 Optimal evaluation ofpairs ofbilinearforms',read(J/'NEW-UNAVAILABLE.json')['restriction'],J/'NEW-UNAVAILABLE.json',J/'guard-ledger.jsonl',{'epubs.siam.org/doi/abs/10.1137/0208037','doi.org/10.1137/0208037'},403),('https://onlinelibrary.wiley.com/doi/10.1002/rsa.70063','Models of Random Spanning Trees 2407.20226/DOI10.1002/rsa.70063','ENTIRE identified work ALL NEW body/METADATA/query/host/version/arxiv/author/cache/mirror/DOI/API/indirect deliveries unavailable afterHTTP403;no retry/alternate recovery. Exactpredeliveryoriginal/authorcopiesonly,notfinalequivalence.',A/'ACTUALBRIEF.md',A/'guard-ledger.jsonl',{'onlinelibrary.wiley.com/doi/10.1002/rsa.70063','doi.org/10.1002/rsa.70063','arxiv.org/abs/2407.20226','arxiv.org/pdf/2407.20226'},403)]
for url,work,restriction,evidence,ledger,keys,status in closures:
 den['blocked_keys']=sorted(set(den['blocked_keys'])|keys);den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower()})
 den['records'].append(dict(url=url,reason=dict(status=status,artifact=work,restriction=restriction),evidence=dict(path=str(evidence),sha256=sha(evidence),guard_sha256=sha(ledger))))
# All integrity checks precede root integration mutations.
save(P/'high-girth-ur-matching-primary-parent-integration-r2.json',records['highgirth']);save(P/'tensor-dominant-orbit-jaja-primary-parent-integration-r3.json',records['jaja']);save(P/'expanded-corpus-r511-parent-integration.json',ar);save(ROOT/'inherited-denials-r524.json',den)
save(ROOT/'highgirth-r2-jaja-r3-r511-intake-report.json',dict(utc=now,files=dict(highgirth=125,jaja=90,r511=120),frozen=77,corpus_bindings=22,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(files=335,frozen=77,corpus_bindings=22,credit=0,accepted_new=57)))
