import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil,base64,ast
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==57
den=json.loads((ROOT/'inherited-denials-r450.json').read_text());den['utc']=now;reports=[]
for name,mname,expected,expected_frozen,terminal in [('expanded-corpus-r448','SHA256-MANIFEST.json',114,13,'terminal_manifest'),('tree-hom-hitting-source-review-sol-r1','MANIFEST.json',113,194,'seal24')]:
 A=P/name;m=json.loads((A/mname).read_text());mf=m['files'];assert isinstance(mf,dict) and len(mf)==expected
 for n,v in mf.items():
  q=A/n;assert q.is_relative_to(A) and not q.is_symlink();assert sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],str(q)
 exclusions=m['precisely_named_terminal_noncircular_exclusions' if name.startswith('expanded') else 'terminal_non_circular_exclusions']
 assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(mf)|set(exclusions)
 f=json.loads((A/'frozen-inputs.json').read_text());assert len(f)==expected_frozen
 for n,h in f.items():
  q=Path(n);assert not q.is_relative_to(P/'expanded-corpus-r450');assert sha(q)==h,n
 after=json.loads((A/'frozen-after.json').read_text());assert after['count']==expected_frozen and after['mismatches']==[]
 receipts=[]
 for q in sorted(A.glob('*.receipt.json')):
  v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
  receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
 assert json.loads((A/(terminal+'.receipt.json')).read_text())['exit']==0
 budget=json.loads((A/'search-budget.json').read_text());charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()]
 prev=dict(calls_used=0,queries_used=0,maximum_calls=3 if name.startswith('expanded') else 2,maximum_queries=9 if name.startswith('expanded') else 6,charged_before_call=True)
 for i,c in enumerate(charges,1):
  assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256']
  plan=json.loads((A/c['plan']).read_text());assert plan['queries']==c['queries'];expected_state=dict(prev);expected_state['calls_used']+=1;expected_state['queries_used']+=len(c['queries']);assert c['after']==expected_state;prev=expected_state
 assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
 events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events)
 assert counts==(dict(attempt=9,success=7,redirect=1,unavailable=1) if name.startswith('expanded') else dict(attempt=1,success=1))
 for e in events:
  if e['event']=='success':assert sha(A/e['destination'])==e['sha256']
  if e['event']=='unavailable':
   assert e['url']=='https://onlinelibrary.wiley.com/doi/pdf/10.1002/jgt.23014' and e['status']==403
   key=urlsplit(e['url']).hostname.lower()+unquote(urlsplit(e['url']).path).rstrip('/')
   den['blocked_keys']=sorted(set(den['blocked_keys'])|{key,'doi.org/10.1002/jgt.23014'})
   den['records'].append(dict(url=e['url'],reason=dict(status=403,artifact='Disjoint total dominating sets near triangulations final DOI10.1002/jgt.23014/source2205.06464',restriction='Entire identified work unavailable ALLnew alternate host/query/version/arxiv/author/DOI/API/cache/mirror body delivery. Existing original saved before denial only where expressly copied; not final equivalence. Distinct Bickle2203.10239 work is not this artifact.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'))))
 report=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/mname),verified_manifest_files=expected,verified_frozen_bindings=expected_frozen,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(v['exit']) for v in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Authenticated live old/new states, exact plan digests/querystrings, final budget and unchanged bookkeeping helper',root_scope='Documentary integrity/provenance/routing only; root did not solve or execute mathematical programs/Lean/checkers',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
 if name.startswith('expanded'):
  rr=json.loads((A/'reservation.json').read_text());gates=json.loads((A/'results.json').read_text());prov=json.loads((A/'originals.json').read_text());assert len(rr['ids'])==20 and set(rr['ids'])==set(map(int,gates))==set(map(int,prov));chunks={}
  for key,row in prov.items():
   q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
   if str(q) not in chunks:
    b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
   h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];assert raw==base64.b64decode(row['raw_line_base64']) and dg(raw)==row['raw_line_sha256'] and row['newline'] and raw.endswith(b'\n')
   obj=json.loads(raw);assert obj==row['record'] and obj['mathdb_id']==int(key)
   for field,v in row['statement_tokens'].items():
    token=re.search(rb'"'+field.encode()+rb'"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
    assert token.decode()==v['raw_token'] and dg(token)==v['raw_sha256'] and json.loads(token)==v['decoded']==obj[field] and dg(obj[field].encode())==v['decoded_utf8_sha256']
  assert budget['calls_used']==3 and budget['queries_used']==9
  for n in ['search-screen-response.json','search-followup-response.json','search-last-response.json']:json.loads((A/n).read_text())
  report.update(root_disposition='ZERO_QUALIFIED_SURVIVORS',verified_original_bindings=sorted(rr['ids']),all20_gates=gates,scientific_summary='353974 original/final Bickle Proposition3.5/Theorem3.6 already public refutation,zero.354612octahedron refutes proper-color literal but properness unsupported by source coupon-coloring domain,zero correction; final23014denied403.350680(c) source-ownTheorem6.13/companion proof; full(b)coefficientwiseHankel positivity remains gap.356877 actual2601.17624primary exact proof claim is concreteHOLD, central90page proof/rank-preserving arbitrary-class reduction unread. Sixteen targets without primary acquisition,seventeen original cited bodies unread. No full survivor.',process='Receipted work/access failure preserved; no source/frozen/helper/budget violation reported; sampled/native/writer limitations retained. No universal compliance or proof clearance from metadata.')
  save(P/'expanded-corpus-r448-parent-integration.json',report)
 else:
  gates=json.loads((A/'keyedreview.json').read_text());assert gates['mathdb_id']==351988 and gates['credit']==0 and not gates['formal_dispatch']
  assert budget['calls_used']==1 and budget['queries_used']==1;json.loads((A/'search1-full-response.json').read_text())
  report.update(mathdb_id=351988,root_disposition='PARKED_SCIENTIFIC_HOLDS_ORDINARY_PASS_RETAINED',review=gates,ordinary='Independent full proof PASS on source-defined n>=2 random-walk domain, singleton equality only with stated absorbing convention; empty source mean undefined, no artificial extension credit',source='Actual copied v4 full9pages/proofs/Figure4 read; v1 and final equivalence UNPAID after final403, no alternate delivery authorized',prior='Actual2014EJCP4.9extremality theorem/proof bounded concrete nonmatch: minimum-W among target-specific maximizers does not order every source pair. Specifically applicable Sidorenko1994 necessary-condition proof403unread, exact Gaussian/Wiener prior NOTcleared.',family='Reviewer personally compared supplied57accepted+39prior full trusted scopes, bounded nonoverlap, no certificate reaudit or extra helper/endpoint count',scientific_holds=['Identified final/source-version/correction body unavailable','Specifically applicable Sidorenko1994 proof unavailable','Current proof-registry evidence access-limited; dated heads only navigation'],significance='No complete routine exclusion established; full arbitrary-pair content may be substantive, conditional on named holds. Neither standard Gaussian tools nor shortness alone excludes. No worldwide novelty claim.',process='Own schema KeyError scopes13 preserved; scopes14 recovered actual accepted-record schemas. No unchanged failure rerun, unauthorized source delivery or helper change reported. Native/writer/transient telemetry limits retained; no universal compliance assertion.')
  save(P/'tree-hom-hitting-source-parent-integration-sol-r1.json',report)
 reports.append(report)
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'10.1002/jgt.23014','2205.06464'})
den['root_r448_neighborhood_scope']='Neighborhood final10.1002/jgt.23014/source2205.06464 denied403 ALLalternate bodydelivery unavailable; originalalreadycachedonlywherecopied,notfinalequivalence. Propercolor354612octahedron is source-domain correction0, not source conjecture refutation. Distinct Bickle353974original2203.10239 andactual2023final public refutation0. Forest350680(b)unpaid/(c)public,matroid356877specific2026primaryproofbody/rankreductionHOLD.'
den['root_tree_hitting_review_r1_scope']='Independent ordinary351988 PASS with source n>=2 and explicitsingleton convention; fullv4 source read,2014extremalityprimary bounded nonmatch,57+39family bounded nonoverlap. ScientificPARK retained: final351988/Sidorenko1994denied/currentregistryevidenceunavailable; no newretrieval lane or formal dispatch. No unsupported routine exclusion, worldwide novelty or sourcefinal equivalence claim.194frozen/113ownmanifest verified;1GETsuccess/1search1query.'
denpath=ROOT/'inherited-denials-r451.json';save(denpath,den)

base_source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();base_tail=base_source[base_source.index('# Metadata selector:'):];base_tail=base_tail[:base_tail.rfind('\nprint(')]
tree=ast.parse((ROOT/'intake-wavelet-r2-prepare-r444.py').read_text());steering0=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='steering' for t in n.targets))
peer_ids={326555,324571,332073,351988};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486','https://arxiv.org/abs/1512.05406','https://arxiv.org/abs/2109.09249'}
meta=json.loads((ROOT/'selection-routing-r450.json').read_text());peer_ids.update(meta['ids']);peer_sources.update(meta['sources'])
ready=[]
for number,other in [(451,452),(452,451)]:
 L=P/f'expanded-corpus-r{number}';assert not L.exists();active=['expanded-corpus-r450',f'expanded-corpus-r{other}']
 tail=base_tail.replace('selection-routing-r434.json',f'selection-routing-r{number}.json').replace('for num in range(421,434):','for num in range(421,450):')
 tail=tail.replace("active=['cmdrr-five-three-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r2']",'active='+repr(active))
 tail=tail.replace("peer_ids={326555,324571};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486'}",'peer_ids='+repr(peer_ids)+';peer_sources='+repr(peer_sources))
 tail=tail.replace("'accepted_new':55","'accepted_new':57").replace('55/60','57/60').replace("'frozen_bindings':12","'frozen_bindings':13")
 tail=tail.replace('Root separated this20 from retained active IDs326555/324571 and primary URLs1310.5240/1211.6486 using immutable metadata.','Root excluded retained r450 and sibling IDs/sourceURLs from root metadata without active-child access; accepted57 and parked351988 excluded.')
 tail=tail.replace("shutil.copyfile(denpath,L/'inherited-denials.json')","shutil.copyfile(ROOT/'charge_search.py',L/'charge_search.py')\nshutil.copyfile(denpath,L/'inherited-denials.json')")
 tail=tail.replace("'historical-results-allowlist.json','TASK.txt']","'historical-results-allowlist.json','TASK.txt','charge_search.py']")
 tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2','binary-projection-ratio-source-review-sol-r1','graph-wavelet-minimax-source-review-sol-r1','graph-wavelet-minimax-primary-comparison-sol-r2','tree-hom-hitting-source-review-sol-r1']:")
 tail=tail.replace('task=core+latest',"core=core.replace('Current55/60 beyond39 prior,94total.','Current57/60 beyond39 prior,96total.').replace('Current accepted55 includes','Current accepted57 includes').replace('Twelve immutable frozen bindings','Thirteen immutable frozen bindings')\ntask=core+latest")
 steering=steering0.replace('ACTIVE expanded-corpus-r442 and expanded-corpus-r443',f'ACTIVE expanded-corpus-r450 and expanded-corpus-r{other}')
 steering+='\nCompleted351988independent source/math/prior/familyreview ORDINARYPASS retained for all source-defined n>=2, explicit absorbing-singleton extension only,emptymean undefined/no endpointcredit. Allv4sourceproofs+Figure4read,actual2014EJCP4.9extremalityprimary boundednonmatch: target-specific maxcount/minW not arbitrarypair order.57+39trustedfamily boundednonoverlap. SCIENTIFICPARK finalDAM3892026DOI10.1016/j.dam.2026.03.043/PIIS0166218X26001903/source2109.09249 andapplicableSidorenko1994DOI10.1016/0012-365X(94)90388-3/PII0012365X94903883 unavailable403,ALLnewalternate bodydelivery denied; currentregistryevidenceunavailable,datedheads navigationonly. No furtherretrieval/formallane,credit0. Specificunreadholdnotgenericworldwideunknownveto; noclassicaltool/shortness-onlyroutineexclusion. Four registryROOTmetadataartifacts504 unavailable:NOroot/README/tree/API/branch/versionalternate refresh/retry/reconstruction; notblanketban everydistinctproofpublication/repo, but cannotindirectlyrestore deniedmetadata.\n'
 steering+='\nCompletedr448all0:new neighborhoodfinal10.1002/jgt.23014/source2205.06464HTTP403 ALLalternatebodydeliveryunavailable,alreadycachedoriginalonlywherecopied,notfinalequivalence.354612propercoloroctahedron literalcorrection0,actualsourceframeworknonpropercouponcoloring unrefuted.353974actualoriginal2203.10239+2023BicklefinalProp3.5/T3.6publicrefutation0,differentworknotdenied.350680(c)actualpublicT6.13/2024companionproof,(b)coefficientwiseHankelpositivityunpaid.356877concrete2601.17624primaryclaim exactpublicproofobstacle,central90pageproof/rank-preservingreductionunread =>specificHOLD. Sixteenwithoutprimaryacquisition/seventeenoriginalbodiesunread. r449all0:actualKeusch352639,source-own344760fieldautomorphismhalfplane/fullsimilarityrefutation,source-own376136strongermatrix/squareenergytheorem public0.338284K1/P4singlevertexendpoint0,nontrivialproductunpaid.346690ONEcoloringALLs,k fixedh notpaidbyfixedk/compactness/twofailedmultiplicativeexamples. Counterhelperlivecontinuityverified. Priorr443latehistoryFAIL,r444inertdot/rootpunctuationambiguity,r446counter-continuityFAIL(noovercapinferred),r447late-registryFAILallretained,noautomaticretroactivequalification. Allrootintakeshash/provenance/routingonly,notmathproofclearance.\n'
 steering+='\nBOOKKEEPING: charge_search.py additionalIMMUTABLEhelper,THIRTEENbindings. BEFOREnativeSEARCH persist plan top-levelqueries EXACTstrings; invoke ABSOLUTEcharge_search.py ownplanpath UNDERrun.py. Helper authenticates liveoldcounters+chargeledger BEFOREmutation,rejectsduplicate/exhaustion,writesviaownwriter. NEVERdirectbudget/chargeledgeredit. Aftercharge nativecallEXACTLYONCE,FULLactualresponse savedIMMEDIATELY beforeotherwork. Wholelane3calls9queries,failedattemptsstaycharged,norefund/reset/backfill. GETsolefixedguard. Beforeinvestment exactIDkeys/scalarIDs AND exactsourceURLhistorymatches actuallyreconciled,noneighbortransfer;readsourceownstrongertheoremsbeforeclaimingnew. Standalonefirsttwocommands,no dot/prosepunctuation. Inertownverifierargumenttrue0/all13checked undercaps recordedinvocationdeviation notautomaticexternalpolicybreach/abandonment. Genuineprotected/frozen/access/cap/network/budgetviolationsretainSTOP/disclosure.\n'
 tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(steering),tail,count=1,flags=re.S)
 ns=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+f'#complete-metadata-r{number}','exec'),ns)
 rr=json.loads((L/'reservation.json').read_text());assert not set(rr['ids'])&peer_ids;assert not {x.get('source_url') for x in rr['rows']}&peer_sources
 peer_ids.update(rr['ids']);peer_sources.update(x.get('source_url') for x in rr['rows'])
 fb=json.loads((L/'frozen-inputs.json').read_text());assert len(fb)==13 and all(sha(Path(n))==h for n,h in fb.items()) and not (L/'bootstrap-receipt.json').exists()
 assert 'Current55/60' not in (L/'TASK.txt').read_text()
 ready.append(dict(lane=str(L),task_sha256=sha(L/'TASK.txt'),ids=rr['ids'],frozen=13,role='research'))
save(ROOT/'r451-r452-ready.json',dict(utc=now,accepted_new=57,target_new=60,intakes=[str(P/'expanded-corpus-r448-parent-integration.json'),str(P/'tree-hom-hitting-source-parent-integration-sol-r1.json')],packets=ready,latest_denials=str(denpath),model='gpt-6.1-sol',reasoning='high',service='default',credit=0))
print(json.dumps(dict(accepted_new=57,intakes=[dict(lane=x['source_lane'],manifest_files=x['verified_manifest_files'],frozen=x['verified_frozen_bindings'],receipt_exit_counts=x['receipt_exit_counts']) for x in reports],packets=ready)))
