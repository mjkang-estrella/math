"""Documentary packet intake and independent-review construction; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;A=P/'expanded-corpus-r510';chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r510.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'SHA256-MANIFEST.json');entries=m['files'];assert len(entries)==151
for name,x in entries.items():
 assert not Path(name).is_absolute() and '..' not in Path(name).parts
 q=A/name;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes']
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'SHA256-MANIFEST.json','manifest_final.receipt.json','manifest_final.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex);frozen(A,13);rec=receipts(A,{'get_quaternion.receipt.json':1})
assert read(A/'manifest_final.receipt.json')['exit']==0
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');assert len(ids)==20 and set(ids)==set(map(int,gates))
prov=read(A/'provenance.json');initial=read(A/'provenance-initial.json');assert len(prov)==20 and set(prov)==set(initial)==set(gates)
sources={}
for key,v in prov.items():
 raw,obj,token=corpus(v);mid=int(key);assert obj['mathdb_id']==mid and (A/'originals'/f'{mid}.jsonl').read_bytes()==raw
 assert all(initial[key][k]==v[k] for k in ['chunk','chunk_sha256','line','raw_sha256','newline','keys'])
 assert list(obj)==v['keys'] and token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and dg(obj['statement'].encode())==v['statement_utf8_sha256'] and obj['statement']==gates[key]['literal_statement'];sources[key]=obj['source_url']
budget=search(A,3,9,3,9,['search1-response.json','search2-response.json','search3-response.json'])
events=guard(A,[q for q in (A/'plans').glob('*.json') if 'url' in read(q)],ids,dict(attempt=7,success=6,redirect=1),6)
assert len(events)==14 and events[-1]['event']=='redirect'
stop=read(A/'NETWORK-STOP.json');assert stop['request']=='https://doi.org/10.17777/pjms.2024.27.4.021'
assert events[-2]['url']==stop['request'] and events[-2]['event']=='attempt'
failout=(A/'get_quaternion.output.txt').read_text();assert 'HTTP' in failout and ('GuardRejected' in failout or 'non-HTTPS' in failout or 'redirect' in failout)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==869
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
summary='r510 zeroqualifiedsurvivors.373070 AUTHOR fullfixedm>=2 dicyclicMSTDconstruction everyintegern>=max(3,2m-1,2^m),2n distinctsets,products4m-4/inverseproducts4m-5;no independentPASS/significancequalification,assignedfullordinary/source/2022primaryadaptationreview. Specific2024Quaternionconstruction/proofUNREAD andnowENTIREworkclosed,not clearedbytotalMSTDcountsnippet; no primary/routine exclusion authenticated.381241 actual2608.02429Prop6.1 publicprojectionproof/strictlimitbridge0;381395limit1/2strictimprovement and373579middleinterpolation unpaid,320075isolateexceptioncorrection0.151manifestfiles20corpusbindings13frozen869savedhistorynames verified;7GEThops6PDFsuccess1DOI302,redirectedHTTPtargetrejectedBEFOREdispatch,loggerthenfailed,no unavailablebackfill/noHTTPfetch/no retryorHTTPSupgrade. Trueget_quaternionexit1 retained; STOP/nonPASS/access/processqualificationpreserved,not universalcompliance.3search9strings. Only4assignedoriginalbodiespassageread,other16unread,no visual/sourcefinal/currentregistryclearance. Sourceheaderdatecorrectionandmaterial/task/denialtruncationlimits/unknownnative-transient-writerpeaksretained. Noformaldispatch/acceptance/credit.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=151,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=rec,guard_events=dict(collections.Counter(e['event'] for e in events)),search_budget=budget,verified_saved_history_names=869,scientific_summary=summary,root_disposition='ZERO_QUALIFIED_SURVIVORS_GUARD_STOP_NONPASS_373070_INDEPENDENT_REVIEW_ASSIGNED',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary integrity/routing only; no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r520.json');den['utc']=now;den['root_r510_scope']=summary
den['blocked_keys']=sorted(set(den['blocked_keys'])|{'doi.org/10.17777/pjms.2024.27.4.021'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'sum and difference sets in generalized quaternion groups','10.17777/pjms.2024.27.4.021','pjms27(4)(2024)773-780'})
den['records'].append(dict(url=stop['request'],reason=dict(status='GuardrejectedHTTPredirectBEFOREdispatch;loggerfailed;no unavailableeventbackfill',artifact=stop['work'],restriction=stop['restriction']),evidence=dict(path=str(A/'NETWORK-STOP.json'),sha256=sha(A/'NETWORK-STOP.json'),failed_receipt=str(A/'get_quaternion.receipt.json'),failed_receipt_sha256=sha(A/'get_quaternion.receipt.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
# All documentary checks precede root mutations.
save(P/'expanded-corpus-r510-parent-integration.json',record);denpath=ROOT/'inherited-denials-r521.json';save(denpath,den)
L=P/'dicyclic-mstd-fixed-size-source-review-sol-r1';assert not L.exists();L.mkdir();(L/'inputs').mkdir()
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/name,L/name)
shutil.copyfile(denpath,L/'inherited-denials.json')
raw=(A/'originals/373070.jsonl').read_bytes();literal=json.loads(raw);(L/'inputs/original373070.raw.jsonl').write_bytes(raw);save(L/'inputs/literal373070.json',literal);save(L/'inputs/provenance373070.json',prov['373070']);save(L/'inputs/author-gates373070.json',gates['373070'])
for name in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','source-read-inventory.json','NETWORK-STOP.json','REPORTING-ERRATA.md','search1-response.json','search2-response.json','search3-response.json']:shutil.copyfile(A/name,L/'inputs'/name)
for name in ['dicyclic.pdf','dicyclic.txt','dihedral.pdf','dihedral.txt']:shutil.copyfile(A/'sources'/name,L/'inputs'/name)
for name in ['dicyclic.json','dihedral.json','quaternion.json']:shutil.copyfile(A/'plans'/name,L/'inputs'/name)
shutil.copyfile(ROOT/'accepted57-review-context.json',L/'inputs/accepted57-scopes.json')
prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,L/'inputs/prior39-scopes.json')
save(L/'reservation.json',dict(ids=[373070],rows=[literal],purpose='Independent full fixed-size dicyclic MSTD construction, exact source/primary adaptation and significance qualification; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
tree=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in tree.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''SOLE373070, Mandal-Neetu2602.09073v1 Definition1.1,Lemma1.3/normalformspp2-3,Conjecture6.2p18: foreachfixedintegerm>=2 existspositiveK_m forallintegern>=K_m,n>=3,numberofMSTD m-subsets ofDic_(4n)>2^(m/2). Distinguishallnincludingeven,allfixedm,strictinequality,totalcountversusproportion,Conjecture6.2versusmajority6.1. MSTD usesALL orderedpairs/repetitionallowed, productAA versusinverseproductAA^-1 as actualsource; personallycheck exactdefinitions/grouporderb²relation andsourceglyphs. No assumedcommutativity/translationinvariance, no creditfor m2,m3oddn ormovingsizem2n.
Independently reconstructbeforeauthorFULL. Mechanismdisclosed: r=m-1,K=max(3,2r+1,2^m),a order2n,b²=a^n,ba^i=a^-i b; forjmod2n, A_j={a,...,a^r}union{a^j b}. Exactlym distinctelements,2n distinctsets viaunique nonrotation,nottranslated-MSTD assumption. Pairtype products rotationinterval[2,2r] size2r-1 plusa^n outside(n>2r); mixednonrotations j+[1,r] andj-[1,r] disjointmod2n;total4r. Inverseproducts rotationinterval[-(r-1),r-1]size2r-1 alreadycontainsidentity;(a^jb)^-1=a^(j+n)b;mixed j+n+[1,r] andj+[1,r] disjoint bymodbounds;total4r-1. Paymod2nwrap/intervalcardinality/cosetdisjointness,bothmixedorders,inverseconvention,r1,m2,nthreshold/odd-even,distinctj/sets,real2^(m/2)strictboundfrom2n. Lowerboundatleast2n NOTexacttotalMSTDcount. No arithmetic/numeric/enumeration program allowed.
SourceTheorem1.4 m2,1.6 m3oddn,1.8-1.9 m2n movingregime doNOT bynotationalchangegivefixedallm. Verifyactualsourceproofbodies/strongerresultsbeforeclaimnew; sourcefinal/version/correctionunpaid, notknownclosed. SupplieddistinctAscoli etal2210.00669v1 actualgeneralizeddihedralsemidirectlaw/formula3,Th1.8 andsmallsizelemmas; authorreadpp2-4/Lemma2.3only, fullSection3 abundanceconstruction/proofandfinal2026chapterUNREAD. Personally read actual relevant wholeprimaryproof and compare involutiveflip b²=1 versusdicyclicshiftb²=a^n. If completeprior-result-to-target reduction exists,payallm/alllargeodd-evenn,subsetsize/count,nonabelianproductorientation/strictness. No generic"progressionsstandard" exclusion. Stateexactearlierprintedresultversusyournewadaptation,notearlierexactrefutationunlessauthenticated.
CRITICAL specificprior: Sum and Difference Sets in Generalized Quaternion Groups,PJMS27(4)(2024)773-780,DOI10.17777/pjms.2024.27.4.021. AuthorshipShankar and2^(2n)totalMSTDlowerbound areSEARCHMETADATAONLY; actualtheorem/proof/parameters/fixed-sizeconstructionUNREAD. WorkENTIRELYCLOSED afterDOI302toHTTPtargetguardrejectionBEFOREdispatch/loggerfailure. ALLNEWbody/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirectdelivery forbidden; no retry,HTTPSupgrade,identitycorrection,alternateproofdelivery ororiginal-workreconstruction. Distinct2022dihedral/original2026dicyclic works notblanketdenied. Total-subsetsbound alone doesNOTprovefixedm; earlierconstructionmaystillfullysubsumeourone. PreservepreciseHOLD ifthisspecificgapremainsandnoindependentcompleteearlierprimarybridgecanresolveit. No nohitnoveltyclearance or public/routineexclusionfromsnippets. Don'ttreatgenericworldwideunknownasautomaticveto orignoreactualspecificunreadcounterclaim.
Strongpositive: deliberatefullallm/alllargenconjecture,uniformexplicitconstructionincludingevenn,notendpointcorrection/instance/majorityclaim. Strongnegative: sparsearithmetic-progression-plus-oneflip may beCOMPLETEroutineadaptationofactualprimaryconstruction,withno broadermajority/proportionadvance. Independentlyadjudicatewithactualprimaryproof/fullbridgeandstrongestopposition; shortproof/smallcardinalityexcessaloneisnotthepolicyreason. Compareall96trustedscopeendpoints(personally,notopicmatching),oneprospectiveMSTDfamily. Noformaldispatchorselfcredit. ConditionaldormantSolbriefonlyifexactordinary/literal/scientificprospectivegatesPASS; sourceclosed/quarantinedhistoricalworkmustnotbypassviaformalization.
Process: previouspacketSTOP/nonPASS/loggerfailureandlatermaterialrecoveriespreserved,notuniversalprocessclearance. YouareNEWindependentreview,mayreadownexplicitpredeliveryPDFcopies butNOToldlane/ROOT/history/embeddedpaths. Obtainindependentproofandactualsourceglyphs; rootintakeisdocumentarynotmathematicalcertification. Sourceheaderactual9Feb2026,earlier10Febdraftreportingerrorretained. FourregistryrootsandAIclaimsindexaimath.robertj1.comclosedasfullinheritedunion; no newdelivery/reconstruction.
'''
peers=['tensor-dominant-orbit-primary-qualification-sol-r2','high-girth-ur-matching-source-review-sol-r1'];task=common.format(lane=L,id=373070,peers=', '.join(peers))+'\nTARGET-SPECIFIC REVIEW\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+list((L/'inputs').iterdir());save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=373070,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers)
save(ROOT/'dicyclic-mstd-review-r1-ready.json',ready);save(ROOT/'selection-routing-dicyclic-mstd-review-r1.json',dict(ids=[373070],sources=[literal['source_url'],'https://arxiv.org/abs/2210.00669'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True));save(ROOT/'r510-completion-boundary-delta.json',dict(utc=now,message=summary,new_protected_peer=L.name,immutable_worker_inputs_unchanged=True,credit=0,accepted_new=57))
print(json.dumps(dict(files=151,frozen=13,bindings=20,receipts=len(rec),events=dict(collections.Counter(e['event'] for e in events)),ready=ready,credit=0,accepted_new=57)))
