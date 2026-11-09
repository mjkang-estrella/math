import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,base64,re,shutil,ast,sys,runpy,contextlib,io
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
A=P/'expanded-corpus-r434';F=P/'shoe-pair-discrepancy-formal-sol-r2'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==55
assert not (P/'expanded-corpus-r435').exists() and not (P/'shoe-pair-discrepancy-formal-sol-r3').exists()
summaries=[]
for r,mid in [(A,None),(F,324571)]:
 m=json.loads((r/'SHA256-MANIFEST.json').read_text());files=m['files'];assert isinstance(files,dict)
 assert all(sha(r/n)==v['sha256'] for n,v in files.items())
 frozen=json.loads((r/'frozen-inputs.json').read_text());assert all(sha(Path(s))==v for s,v in frozen.items())
 after=json.loads((r/'frozen-after.json').read_text());assert after['count']==len(frozen) and not after['mismatches']
 ex=m.get('terminal_self_exclusions',m.get('terminal_noncircular_self_exclusions'))
 rec=[]
 for n,v in files.items():
  if n.endswith('.receipt.json') or n.startswith('receipt/') and n.endswith('.json'):
   j=json.loads((r/n).read_text());rec.append({'path':n,'exit':j.get('exit'),'sha256':v['sha256'],'guard':j.get('guard',j.get('killed')),'group_members_left':j.get('group_members_left')})
 for n in ex:
  if n.endswith('.receipt.json') or n.startswith('receipt/') and n.endswith('.json'):
   j=json.loads((r/n).read_text());rec.append({'path':n,'exit':j.get('exit'),'sha256':sha(r/n),'guard':j.get('guard',j.get('killed')),'terminal':True})
 record={'utc':now,'lane':str(r),'manifest_files_verified':len(files),'manifest_mismatches':[],'frozen_bindings_verified':len(frozen),'frozen_mismatches':[],'frozen_after':after,'terminal_self_exclusions':ex,'receipt_count':len(rec),'receipt_exit_counts':dict(collections.Counter(str(x['exit']) for x in rec)),'receipts':rec,'accepted_new':55,'target_new':60,'previous_accepted':39,'credit':0,'root_execution':'Documentary integrity and orchestration only; no mathematical programs or compiler/checker execution'}
 if r==A:
  reserve=json.loads((A/'reservation.json').read_text());ids=reserve['ids'];assert len(ids)==20 and len(set(ids))==20
  assert sha(A/'reservation.json')==(A/'reservation.sha256').read_text().split()[0]
  chunks={};prov=json.loads((A/'original-provenance.json').read_text());assert len(prov)==20
  for row in prov:
   cp=Path(row['chunk'])
   if str(cp) not in chunks:
    b=cp.read_bytes();chunks[str(cp)]=(dg(b),b.splitlines(keepends=True))
   h,lines=chunks[str(cp)];assert h==row['chunk_sha256']
   raw=lines[row['line_one_based']-1];assert raw==base64.b64decode(row['raw_line_base64']) and raw.endswith(b'\n') and dg(raw)==row['raw_line_sha256']
   assert raw==(A/'literal'/f"{row['id']}.jsonl").read_bytes()
   obj=json.loads(raw);assert obj['mathdb_id']==row['id'] and obj==row['object']
   token=re.search(rb'"statement"\s*:\s*("(?:\\.|[^"\\])*")',raw).group(1)
   assert token==base64.b64decode(row['raw_statement_token_base64']) and dg(token)==row['token_sha256']
   assert json.loads(token)==obj['statement'] and dg(obj['statement'].encode())==row['decoded_utf8_sha256']
  gates=json.loads((A/'results.json').read_text());assert set(map(int,gates))==set(ids)
  prev='0'*64;events=[]
  for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
   e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
   if e['event']=='success':assert sha(A/e['destination'])==e['sha256']
  assert sum(e['event']=='attempt' for e in events)==16 and sum(e['event']=='success' for e in events)==16
  assert not any(e['event']=='unavailable' for e in events)
  budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
  for i in [1,2,3]:assert isinstance(json.loads((A/f'search-{i}-full-response.json').read_text()),str)
  record.update({'all20_author_gates':gates,'literal_bindings_verified':ids,'all_raw_tokens_and_decoded_bindings_verified':True,'guard_chain_verified':True,'guard_last_sha256':prev,'GET_hops':16,'GET_successes':16,'new_unavailable_artifacts':[],'search_calls':3,'search_query_strings':9,'root_disposition':'NO_QUALIFIED_SURVIVOR:349307exactpublicDing-Yan2608.15521+Han-Mao-ZengJfractionbridgezero;356364source-owncycleinvariant/domainomissioncorrectionzero;354623ownsourcev3counterexampleszero;354571full2balanceddecompositionunpaid. No independent acceptance or formal dispatch.','proof_scope_and_limits':'Actual public proof bodies and full target bridges documented in SUSTAINED-ORDINARY-ROUTES. Presentation/variable typos and unread final/figure scopes remain explicit; no oldopenlabel/source metadata alone grants novelty. Known remembered results without bodies are holds, not new exclusions.','procedural_limits':'Wrong schema key in initial provenance reader failed and was repaired after schema inspection; preserved nonpass. No mathematical programs; native/writer peaks and sampling transients unavailable, no universal cgroup claim.'})
  output=P/'expanded-corpus-r434-parent-integration.json'
 else:
  state=json.loads((F/'results/CHECKPOINT.json').read_text());assert not state['formal_endpoint_present']
  assert all(sha(F/n)==v for n,v in state['files'].items())
  replay=json.loads((F/'results/PARTIAL-REPLAY.json').read_text());assert replay['initial_build_empty']
  for row in replay['records']:
   mod=row['module'];assert sha(F/'src'/f'{mod}.lean')==row['source_sha256']==row['copied_source_sha256']
   assert sha(F/'replay/build'/f'{mod}.olean')==row['post_checker_olean_sha256']
  latest={}
  for n in files:
   if n.startswith('receipt/') and n.endswith('.json'):
    j=json.loads((F/n).read_text());lab=j.get('label','')
    if lab.startswith('lean_') or lab.startswith('leanchecker_'):
     if lab not in latest or int(j.get('stamp',0))>latest[lab].get('stamp',0):latest[lab]={'path':n,'exit':j.get('exit'),'stamp':int(j.get('stamp',0))}
  for row in replay['records']:
   mod=row['module'];assert latest['lean_'+mod]['exit']==0 and latest['leanchecker_'+mod]['exit']==0
  record.update({'mathdb_id':324571,'status':'VERIFIED_PARTIAL_NOT_LITERAL_ENDPOINT','state':state,'partial_replay':replay,'latest_compile_checker_receipts':latest,'production_vs_auxiliary':'Eight core model/probability modules plus positive controls and named-axiom audit = ten checked modules; not ten resolved mathematical endpoints.','root_disposition':'Continue remaining stochastic block estimates/minorization and countableTV/supremum/source-relabeling endpoint from paid foundations. No helper credit or acceptance.','audit_limit':'62 named-declaration transitive axiom reports only; wholeenvironment/private/generated/bodyorigin DAG and completed-endpoint closure unpaid.','controls_limit':'NegativeSameSide exit1 has a secondary failed subproof, not isolated mutation evidence; rework clean controls.','process_deviations':state['deviations'],'prior_limit':'Galbraith-Holmes2012body404 remains unread; no new retrieval or worldwide novelty claim.'})
  output=P/'shoe-pair-discrepancy-formal-parent-integration-sol-r2.json'
 save(output,record);summaries.append({'lane':str(r),'files':len(files),'frozen':len(frozen),'receipts':len(rec),'exit_counts':record['receipt_exit_counts'],'integration':str(output)})

# No new unavailable artifact in r434. Create a new inherited union without altering frozen old files.
den=json.loads((ROOT/'inherited-denials-r434.json').read_text());den['utc']=now
den['root_r434_outcome']='16successfulGETs,no newdenials; all inherited artifact-wide refusals remain. Public/source-own exclusions349307/356364/354623 confer no credit. ActiveCMDRR/shoeformal remain unaccepted.'
denpath=ROOT/'inherited-denials-r435.json';save(denpath,den)

# Reuse only the metadata preparation section; never re-execute prior review integration.
template=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text()
tail=template[template.index('# Metadata selector:'):]
tail=tail[:tail.rfind('\nprint(')]
tail=tail.replace('selection-routing-r434.json','selection-routing-r435.json').replace('for num in range(421,434):','for num in range(421,435):')
tail=tail.replace('shoe-pair-discrepancy-formal-sol-r2','shoe-pair-discrepancy-formal-sol-r3')
tail=tail.replace('task=core+latest',"task=core+latest+'\\nLATEST r434 outcome:349307exactpublic2608.15521jointcycleJfractionbridge;356364sourceowncycleinvariant/exceptioncorrection;354623sourcev3cochordalcounterexamples—allzero.3545712balanced2spanningtrees safe-reconstruction/exchange/discharging gaps.16successfulGETs,3search9queries,12frozenintact,no newdenial. Source/publicproof bodies read at recorded depths, figures/finallimits explicit. Shoes completed8core+controls/audit10module partial; remaining blockminorization/TV/supremum unpaid, continuationr3planned. No formal acceptance or newcredit.\\n'")
L=P/'expanded-corpus-r435'
exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+'#metadata-only-r435','exec'),globals())

# Fresh formal continuation, source-only baseline. Generic instructions are data, not old prep execution.
tree=ast.parse((ROOT/'intake-shoe-cmdrr-and-prepare-formal.py').read_text())
common=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
Q=P/'shoe-pair-discrepancy-formal-sol-r3';Q.mkdir();origins={};base=P/'flat-balance-bridges-formal-pi-r5'
def cp(src,rel):
 dst=Q/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]={'path':str(src),'sha256':sha(src)}
for n in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh']:cp(base/n,n)
for n in ['src','build','audit','receipt','logs','tmp','cache','results','manuscript','output/pdf']:(Q/n).mkdir(parents=True,exist_ok=True)
cp(F/'PINS.json','PINS.json');pins=json.loads((Q/'PINS.json').read_text());assert sha(Path(pins['lean_bin']))==pins['lean_sha256'] and sha(Path(pins['leanchecker_bin']))==pins['leanchecker_sha256']
pack=Path(pins['packages_root']);bins=Path(pins['lean_bin']).parent
upstream=[str(pack/n/'.lake/build/lib/lean') for n in ['mathlib','batteries','aesop','Qq','proofwidgets','importGraph','LeanSearchClient','plausible']]
(Q/'env.sh').write_text('#!/bin/bash\nset -eu\nLANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)\nLEAN_BIN='+str(bins)+'\nexport PATH="$LEAN_BIN:$PATH"\nexport LEAN_PATH="$LANE/build:'+':'.join(upstream)+'"\n')
for q in (F/'inputs').rglob('*'):
 if q.is_file():cp(q,'inputs/original/'+str(q.relative_to(F/'inputs')))
for n in ['SUMMARY.md','results/CHECKPOINT.json','results/PARTIAL-REPLAY.json','results/324571.json','SHA256-MANIFEST.json']:
 cp(F/n,'inputs/previous/'+n)
for row in replay['records']:
 mod=row['module'];cp(F/'src'/f'{mod}.lean',f'inputs/baseline-src/{mod}.lean');cp(F/'src'/f'{mod}.lean',f'src/{mod}.lean')
cp(P/'shoe-pair-discrepancy-formal-parent-integration-sol-r2.json','inputs/ROOT-INTEGRATION.json');cp(denpath,'inputs/INHERITED-DENIALS.json')
save(Q/'INPUT-ORIGINS.json',origins)
detail='''CONTINUATION MathDB324571, full literal all-discrete-law strictSUPdiscrepancy bound. Existing8core modules pluscontrols/audit10compiled/checked and partial source-onlyreplay are paid; NOendpoint or boundpresent. Read inputs/previous/results/CHECKPOINT.json, SUMMARY and full ordinaryproof/review/source under inputs/original. Preserve PMF Natcolors/infiniteiid/cylinder/chronologicalfirstmatch/winningLaw/pairLaw/termination definitions and their exact indexing. Do not start a second model or redo paid stopping theory. Rootonlyverifiedintegrity, not independent source-body acceptance of formal definitions. If a true fidelitygap requires change, editONLYownworkingsrc and documentdiff/rebuild; frozenreferencecopiesimmutable.
After mandatory reads/pins, coldcompile baseline10 in recordedPARTIAL-REPLAY dependencyorder in OWNbuild (ShoeBase,Probability,Stopping,Block,Pair,Conditional,Diagonal,Termination,Controls,AxiomAudit). This baselinepreflight is an explicit exception before firstNEWproofwrite; no legacyoleans copied/imported. FIRSTNEWPROOFoperation write a real isolated/block probability estimate module (e.g.ShoeBlockProbability.lean) and strictcheck beforebroadAPIprobes. Aim at E_abprobability/othercolorcollision/unionbound, not more restatingsemantics or an arithmetic-only terminalhelper. Later actualdiagnostic-guidedAPIreads/probes allowed undercappedrunner. Persistpaidgreencheckpoints and continue to FULL endpoint.

Outstanding pipeline from independently paidordinaryproof: realcollisionmasss>0,s<=1 andcoordinatep_i<=sqrt(s); zero/pointmass/large-s branches. For smalls<1/64, K=floor1/(4sqrt(s))>=2,K>=1/(8sqrt(s)),K^2s<=1/16,Kp_i<=1/4. Exactfinite-cylinder probability of isolatedE_ab =p_i^2(1-p_i)^(2K-2); genuine conditioning or fullyprovedequivalentunconditionalestimate for non-iotherpair collisions, countable color sums <=s/(1-p_i)^2, finite union(K-1)^2 bound<=4/49<1/2. No assumption theseoverlappingpairevents independent. Existing GoodBlockwinner inclusion and isolatedpositionuniqueness shouldbeconsumed, not assumednew. Bernoulli power>=1/2, disjointK^2GoodBlockevents lowerbound TRUEwinningLaw, yielding y_i>=p_i^2/(256s)=pairLaw_i/256. LargebranchalreadywinningLaw>=p_i^2 ands>=1/64; full all-branchminorization. Pay ENNReal/real/PMFcoercions,finiteness,division,zero,s1,K2 correctly.
FullcountableTV half-l1/overlap/sup-subsets identities (absolute convergence), min>=x/256 ->D<=255/256, strictuniversalSUP<=255/256<1, notjust eachD<1. Arbitrary countablecolors relabeling/finitezeroextension invariance and source model correspondence; sourceXnormalizedindependentpair conditionalmatch law and YactualSTRICTL1,R1,L2,R2 chronologicalwinner, no Poisson/randomside/simultaneouspair shortcut. Existinga.s.termination/ae fallback invariant mustbeused toremove fallback influence. Avoid any endpoint conditionalon assumedminorization/boundor arithmetic-only surrogate. Original/finalConjecture4eq19,NOTConjecture5/optimalconstant.

Fullwholeenvironment inclprivate/generated/transitivebodyoriginDAGaudit, exactendpointclosures/allowedaxioms; old62namedreports insufficient. Positivecontrols actualsource/universality, clean intentional semanticnegativecontrols with isolated expectedfail cause (oldNegativeSameSide hadsecondaryfailedsubproof; preserveashistoricalnonpass,rework). ALLnew+baseline source-onlyEMPTYbuildreplay/checkers andpostcheckerhashes; no globalaggregateRSSclaim acrossjobs. FinishreadablepaperPDFallpagesvisuallyinspected. No paper authoring/replayhelper canoverwritePINS. Independentfinalsource/proof/deepaudit/manuscriptreview androotacceptance stillseparate.

Newlane MUSTavoid earlier deviations: no runner --help, no runpy-sourceinspection withoutcaps, no runpywrapper asalternateCLI, no concurrentreplay/negativejobs; ALLexecutionSEQUENTIAL underexactsuppliedrunnerCLI, controlledlogdisplaythroughrunner. Preserve inheritedexceptions/failures inprocessrecord, no silentwaiver. Everyjobtrueexit/fullreceipthashes/reaped, samplingnotcgroupperfection. Galbraith-Holmes2012body404unreadlimit/no worldwidepriorityclaim remains. Nochildren/network. Do notvoluntarilystopathelpermilestone; fullpipelineuntilcompletion or honestinterruptioncheckpoint. Credit0,campaign55/60 beyond39unchanged.'''
task='FULLshoe324571 continuation in '+str(Q)+'. PROTECTEDACTIVE/PLANNEDPEERS cmdrr-five-three-formal-sol-r3,expanded-corpus-r435: NOread/hash/glob/list/poll evenmetadata.\n'+common.replace('LANE',str(Q))+'\nSPECIFIC SCOPE:\n'+detail
(Q/'TASK.txt').write_text(task)
save(Q/'ROOT-PREP.json',{'utc':now,'lane':str(Q),'mathdb_id':324571,'model':'gpt-6.1-sol','provider':'codex','reasoning_effort':'high','service_tier':'default','children':False,'network':False,'accepted_new':55,'credit':0,'no_old_oleans_copied':True,'root_role':'Documentary source-only continuation preparation','baseline_order':[x['module'] for x in replay['records']]})
frozen={str(q):sha(q) for q in F.rglob('*') if q.is_file()}
for q in (Q/'inputs').rglob('*'):
 if q.is_file():frozen[str(q)]=sha(q)
for n in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh','PINS.json','env.sh','TASK.txt','INPUT-ORIGINS.json','ROOT-PREP.json']:frozen[str(Q/n)]=sha(Q/n)
assert all(sha(Path(s))==v for s,v in frozen.items());save(Q/'frozen-inputs.json',frozen)
save(ROOT/'r435-shoe3-ready.json',{'utc':now,'intakes':summaries,'shoe_lane':str(Q),'shoe_frozen':len(frozen),'shoe_task_sha256':sha(Q/'TASK.txt'),'discovery_lane':str(P/'expanded-corpus-r435'),'discovery_task_sha256':sha(P/'expanded-corpus-r435/TASK.txt'),'active_other':'cmdrr-five-three-formal-sol-r3','latest_denials':str(denpath),'accepted_new':55,'credit':0})
print(json.dumps({'intakes':summaries,'shoe_ready':str(Q),'shoe_frozen':len(frozen),'discovery_ready':str(P/'expanded-corpus-r435')}))
