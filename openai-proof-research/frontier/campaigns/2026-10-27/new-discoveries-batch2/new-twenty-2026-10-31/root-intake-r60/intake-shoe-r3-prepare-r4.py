import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,ast,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';R=P/'shoe-pair-discrepancy-formal-sol-r3';L=P/'shoe-pair-discrepancy-formal-sol-r4';D=P/'expanded-corpus-r436'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert not L.exists() and not (D/'bootstrap-receipt.json').exists()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==55
m=json.loads((R/'SHA256-MANIFEST.json').read_text());files=m['files'];assert all(sha(R/n)==v for n,v in files.items())
frozen=json.loads((R/'frozen-inputs.json').read_text());assert len(frozen)==395 and all(sha(Path(s))==v for s,v in frozen.items())
after=json.loads((R/'frozen-after.json').read_text());assert after['count']==395 and not after['mismatches']
state=json.loads((R/'results/CHECKPOINT.json').read_text());replay=json.loads((R/'results/REPLAY.json').read_text());order=json.loads((R/'production-modules.json').read_text());assert len(order)==20 and replay['initial_build_empty'] and replay['source_only']
assert order==replay['production_order'];assert sha(R/'src/ShoeEndpoint.lean')==state['formal_endpoint_source_sha256']
for row in replay['records']:
 mod=row['module'];assert sha(R/'src'/f'{mod}.lean')==row['source_sha256']==row['extracted_source_sha256']
 assert sha(R/'build'/f'{mod}.olean')==row['working_olean_sha256']
 assert sha(R/'replay/build'/f'{mod}.olean')==row['post_checker_replay_olean_sha256']
 for phase,runs in row['runs'].items():
  assert runs and runs[-1]['exit']==0,(mod,phase)
  for run in runs:
   q=R/run['path'];assert sha(q)==run['sha256'];j=json.loads(q.read_text());assert j['exit']==run['exit']
   assert sha(Path(j['log']))==j['log_sha256'] and j['group_members_left']==[]
rec=[];memory=[]
for n,v in files.items():
 if n.startswith('receipt/') and n.endswith('.json'):
  j=json.loads((R/n).read_text());r={'path':n,'sha256':v,'label':j.get('label'),'exit':j.get('exit'),'guard':j.get('guard'),'group_members_left':j.get('group_members_left')};rec.append(r)
  if j.get('exit')==-6:memory.append(r)
for n in m['terminal_self_exclusions']:
 if n.startswith('receipt/') and n.endswith('.json'):
  j=json.loads((R/n).read_text());rec.append({'path':n,'sha256':sha(R/n),'label':j.get('label'),'exit':j.get('exit'),'guard':j.get('guard'),'group_members_left':j.get('group_members_left'),'terminal':True})
parent=P/'shoe-pair-discrepancy-formal-parent-integration-sol-r3.json'
record={'utc':now,'mathdb_id':324571,'source_lane':str(R),'manifest_files_verified':len(files),'manifest_mismatches':[],'frozen_verified':395,'frozen_mismatches':[],'frozen_after':after,'receipt_count':len(rec),'receipt_exit_counts':dict(collections.Counter(str(x['exit']) for x in rec)),'receipts':rec,'memory_failure_receipts':memory,'state':state,'replay':replay,'endpoint':'Shoe.source_strict_universal_supremum','source_sha256':state['formal_endpoint_source_sha256'],'root_status':'CHECKED_NAT_ENDPOINT__NOT_TECHNICAL_PASS_OR_ACCEPTED','root_disposition':'Continue relabeling/finite-support zero-extension source certificates and complete memory-bounded all-production body-origin audit, then full independent review. Named endpoint axioms/fresh20module replay do not pay deep audit or generic transport gaps.','module_scope':'Twenty checked proof/control/named-audit modules, not twenty mathematical results. Classify core vs auxiliary modules explicitly in next full audit.','memory_diagnosis_scope':'Failed ShoeDeepAudit serializes bodies/dependencies for the entire imported environment, not only reachable production closures; exact three failed attempts retained. Root only reads diagnostics, does not run Lean.','unpaid':state['unpaid'],'historical_deviations':state['deviations'],'prior_limit':'Galbraith-Holmes2012body404unread, bounded prior qualification only, no worldwide novelty claim.','credit':0,'accepted_new':55,'target_new':60,'previous_accepted':39,'root_execution':'Documentary integrity/orchestration only; no mathematical/Lean execution'}
save(parent,record)

L.mkdir();origins={};base=P/'flat-balance-bridges-formal-pi-r5'
def cp(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]={'path':str(src),'sha256':sha(src)}
for n in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh']:cp(base/n,n)
runner=L/'runner.py';text=runner.read_text();anchor="    lane = os.path.dirname(os.path.abspath(__file__))\n";assert text.count(anchor)==1;oldhash=sha(runner);runner.write_text(text.replace(anchor,anchor+"    os.chdir(lane)  # Root guard: child commands start in their exclusive lane.\n",1))
save(L/'RUNNER-DELTA.json',{'old_generic_sha256':oldhash,'new_sha256':sha(runner),'change':'Own-lane chdir before child dispatch, no caps/reap/logging changes','scope':'New r4 packet only; no active/frozen old helper mutation'})
for n in ['src','build','audit','receipt','logs','tmp','cache','results','manuscript','output/pdf']:(L/n).mkdir(parents=True,exist_ok=True)
cp(R/'PINS.json','PINS.json');pins=json.loads((L/'PINS.json').read_text());assert sha(Path(pins['lean_bin']))==pins['lean_sha256'] and sha(Path(pins['leanchecker_bin']))==pins['leanchecker_sha256']
pack=Path(pins['packages_root']);bins=Path(pins['lean_bin']).parent
upstream=[str(pack/n/'.lake/build/lib/lean') for n in ['mathlib','batteries','aesop','Qq','proofwidgets','importGraph','LeanSearchClient','plausible']]
(L/'env.sh').write_text('#!/bin/bash\nset -eu\nLANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)\nLEAN_BIN='+str(bins)+'\nexport PATH="$LEAN_BIN:$PATH"\nexport LEAN_PATH="$LANE/build:'+':'.join(upstream)+'"\n')
display='''import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(10,10))
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
from pathlib import Path
import sys,json,time,hashlib
lane=Path(__file__).resolve().parent
name=sys.argv[1];assert Path(name).name==name and name.endswith('.log')
q=(lane/'logs'/name).resolve();assert q.parent==lane/'logs' and q.is_file()
offset=int(sys.argv[2]);length=min(int(sys.argv[3]) if len(sys.argv)>3 else 12000,16384)
assert offset>=0 and 0<length<=16384
with q.open('rb') as f:f.seek(offset);b=f.read(length)
record={'utc':time.time(),'log':name,'offset':offset,'length':len(b),'chunk_sha256':hashlib.sha256(b).hexdigest(),'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':10,'AS_limit_bytes':512*1024**2,'outer_timeout_s':20,'scope':'Prospective own-log display exception, self caps only; no sampled group/native display telemetry'}
with (lane/'DISPLAY-CALLS.jsonl').open('a') as f:f.write(json.dumps(record)+'\\n')
print(json.dumps(record),flush=True)
sys.stdout.buffer.write(b);sys.stdout.buffer.write(b'\\n');sys.stdout.buffer.flush()
'''
(L/'display_log.py').write_text(display)
for q in (R/'inputs').rglob('*'):
 if q.is_file():cp(q,'inputs/original/'+str(q.relative_to(R/'inputs')))
for n in ['SUMMARY.md','PAPER.txt','production-modules.json','results/CHECKPOINT.json','results/REPLAY.json','results/324571.json','results/FAILURES.json','results/SOURCE-MAP.json','results/INVENTORY.json','SHA256-MANIFEST.json','output/pdf/shoe-discrepancy-report.pdf']:
 cp(R/n,'inputs/previous/'+n)
for mod in order:
 cp(R/'src'/f'{mod}.lean',f'inputs/baseline-src/{mod}.lean');cp(R/'src'/f'{mod}.lean',f'src/{mod}.lean')
cp(R/'src/ShoeDeepAudit.lean','inputs/failed-audit/ShoeDeepAudit.lean')
for row in memory:
 cp(R/row['path'],'inputs/failed-audit/'+Path(row['path']).name)
 j=json.loads((R/row['path']).read_text());cp(Path(j['log']),'inputs/failed-audit/'+Path(j['log']).name)
cp(parent,'inputs/ROOT-INTEGRATION.json');cp(ROOT/'inherited-denials-r436.json','inputs/INHERITED-DENIALS.json')
save(L/'INPUT-ORIGINS.json',origins)
tree=ast.parse((ROOT/'intake-shoe-cmdrr-and-prepare-formal.py').read_text())
common=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
detail='''Finish completion gates for MathDB324571. Existing NATsourceendpoint Shoe.source_strict_universal_supremum isstrict/checker/freshreplaygreen, fullactualiiD/strictalternation/minorization/countableTV/conditionalpair/a.s.fallbackbridgesin20source/proof/control/named-auditmodules. Read currentSUMMARY/CHECKPOINT/SOURCE-MAP/REPLAY, complete source/literal and independentordinaryreview undercopiedinputs. Preserve all mathematical definitions/proofs except justifiedownsourcecorrections; no new model/duplicateelementaryinequalityproof. Frozenreferencecopiesneveredited; ownworkingsrcauthedwithdocumenteddiff. SourceNatmodel includeszeros/infinite support; generalcountabletransport/finitezeroextensionstillUNPAID, notwaivedbyhavingtheNatbound.

MANDATORYPROCESS: everyexec_command setsworkdir=OWNabsoluteLANE. Newrunnerforcesowncwd; norecursiveworkspaceinventories/runner--help/runpyalternateCLI, no overlappingjobs, no parent/proc-fd/ttyworkarounds. ProspectiveOWNLOGDISPLAYEXCEPTION: use `timeout 20 python3 -I -B LANE/display_log.py LOG_BASENAME OFFSET [LENGTH<=16384]` toseeownsavedrunnerlogs; helperfrontcapsaffinity2/CPU10/AS512MiB and recordsDISPLAY-CALLS.jsonl. Thisisexplicitauthorizedstandalonedocumentarydisplayexception, notcompiler-runnerexecution, no sampledgroup/nativeUItelemetry. Allsource/API/compile/audit/replayreads remainimmutablecappedrunner; theirsavedlogsmaybedisplayedbyhelper. No externalpath/embeddedprovenancefollowing. Frozenhelper/PINSunchanged. Retain historicaluncappeddisplay/runpy/overlap/renderfailures attheiractualstage, notblanketwaiveor falselysaypapernevercompletednow.

Coldstrictbuild20baselineinrecordedorder aftermandatoryreads/pins, NOoldoleans. Then firstNEWPROOFwrite actual relabel/finitezeroextension certificate module (e.g.ShoeRelabel.lean) followedstrictcheck beforebroadAPI. Prove source-faithful encoding of arbitrary countablecolorlaw intoNat, independence/productmeasuretransport underinjectivecolorcoding, firstmatchingtime+winnercolorcorrespondence (handlefallbackonlya.s.), conditionalpairlawanddiscrepancytransport, and finitealphabet/zeroextension specialcase. Actualsource colorsnumberedNat maymakeNatendpointdirectliteral, but explicitnormalization/promisedtransportcertificates stillrequired; do not asserttransportfromthefinalinequalityalone orintroduceassumedlawrelations. No silentfinite-support restriction or Poisson/randomside/simultaneouspair replacement. New generic endpoint shouldCONSUME existingNat theorem throughprovedsemanticbridges. Ifsomeextra abstraction isnotnecessarytosource,stateexactscopeandpayrequirednormalization ratherthaninventingnewproblem. Allcountablezeromass/singlepoint/finitesupportcases paid, sourcehypothesesonly.

DEEP AUDITREPAIR: inputs/failed-audit contains exactprevious3OOM(-6)attemptsunder-M3500. FailedShoeDeepAuditserializesbody/typeedgesforEVERYimportedconstant; donotrepeatunchangedorraisecaps. Enumerateactualproductionmodule-origin declarationsinclprivate/generated first; auditALLthoseandtheirtransitivelyREACHABLEbody/typeconstants, notunrelatedunusedMathlibuniverse. EndpointclosuresmustexplicitlyincludeShoe.source_strict_universal_supremum,newtransportendpoint,winningLaw_minorization,sourceTV_eq_countableTV,sourceY_eq,conditionalColorMeasure_toPMF. Useactualvisitedset/sharedmemoization, noExpressionprettyprinting, streamname/origin/type/bodydependencies/axiom/safetyflags once. SplitROOTSinto boundedsequentialprocessbatchesifneeded, allwithinunchangedj1/M3500/caps; exportcompleteperbatchclosure, merge/deduplicateexternalJSONdocumentaryauditmetadatawithconsistencyassertions. Eachbatchmustfinishrealexit0, no skippednodes/prefix-as-full. Pythonmergeofalreadyexportedmetadataexplicitlyallowed; mathematicalPython/solversstillforbidden. Enumeratecoreproofvscontrolvsnamed-audit/toolmodulesseparately; audittoolsnotimportedintomathematicalendpointorcreditedasproofs. Onlypropext/Classical.choice/Quot.sound transitively; exactfinalcounts/closures/originsfromactualdata. Named#printaxiomstrioaloneNOTdeepaudit. FreshLeancheckerrequiredallproductionmodules; no trustedmissingbody/currentaxiom maskedbyclosedtheoremproof.

CloseALLgatesbeforetechnicalPASS: cleansemanticpositive+isolatedmutationnegativecontrols, newcolortransportcontrols, allnew+baselinefreshsource-onlyEMPTYbuildstrict+checkerwithupstreamONLY andsourcepostcheckerhashmatch; nooldoleancopy. Updatefinishedreadablepaperwithcompletecurrenttheorem/sourcePMF/supremum/transport/audit/replay, rigorousordinaryunconditional4coordinatebridgeimplementation andretainedprior/processlimits. Current3pagePDFisimmutableinput; createownupdatedPDFwithPDFskillmarkerexactONCEinthislaneandallpagevisualQA, nodupmarkerforeachrendererretry. Historicalpaper'sunpaidstatementsmustberevisedaroundactualfinalstate, butfailedattemptsremaininprocessappendix. Galbraith-Holmes2012body404unread andboundednoveltylimitremain, nonetwork. Fullindependentstatement/proof/deepbody/manuscriptreview androotacceptance stillseparate. No selfcredit;55/60 beyond39. Continueuntilfullcompletiongates orhonestprecisepartialcheckpoint, notacknowledgment-only.'''
detail=detail.replace('OWNabsoluteLANE',str(L)).replace('LANE/display_log.py',str(L/'display_log.py'))
task='Fullshoe324571completionrepairin '+str(L)+'. PROTECTEDACTIVE/PLANNEDPEERS cmdrr-five-three-formal-sol-r4,expanded-corpus-r436: NOread/hash/glob/list/poll evenmetadata.\n'+common.replace('LANE',str(L))+'\nSPECIFIC SCOPE:\n'+detail
(L/'TASK.txt').write_text(task)
save(L/'BASELINE-ORDER.json',{'order':order,'scope':'20checkedproof/control/named-auditmodules,NOT20results; classifyactualcore/tooloriginsduringfullaudit','no_old_oleans_copied':True})
save(L/'ROOT-PREP.json',{'utc':now,'lane':str(L),'id':324571,'model':'gpt-6.1-sol','provider':'codex','reasoning_effort':'high','service_tier':'default','children':False,'network':False,'accepted_new':55,'credit':0,'root_role':'Documentaryintegrity/orchestrationandgenericprocesswrappers only','own_cwd_guard':True,'own_log_display_exception':True})
frozen={str(q):sha(q) for q in R.rglob('*') if q.is_file()}
for q in (L/'inputs').rglob('*'):
 if q.is_file():frozen[str(q)]=sha(q)
for n in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh','PINS.json','env.sh','TASK.txt','INPUT-ORIGINS.json','ROOT-PREP.json','RUNNER-DELTA.json','BASELINE-ORDER.json','display_log.py']:frozen[str(L/n)]=sha(L/n)
assert all(sha(Path(s))==v for s,v in frozen.items());save(L/'frozen-inputs.json',frozen)

# Update only the unlaunched discovery packet's peer/version routing; reservation unchanged.
df=json.loads((D/'frozen-inputs.json').read_text());assert all(sha(Path(s))==v for s,v in df.items())
t=(D/'TASK.txt').read_text().replace('shoe-pair-discrepancy-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r4')
t+='\nLATEST SHOE324571: completedr3actualNatPMFsourceuniversalSUP<=255/256<1strict/checker/replaygreen;NOTtechnicalPASSoraccepted. Genericcountabletransport/finitezeroextensionandwholebodyoriginDAGauditunpaid,3auditOOM(-6);r4repairactive/planned. DoNOTrecountsamefamily;0credit55/60.\n'
(D/'TASK.txt').write_text(t);df[str(D/'TASK.txt')]=sha(D/'TASK.txt');(D/'frozen-inputs.json').write_text(json.dumps(df,indent=2)+'\n')
for q in [D/'ROOT-PREP.json',ROOT/'selection-routing-r436.json',ROOT/'r436-ready-after-cactus.json']:
 j=json.loads(q.read_text());j['task_sha256']=sha(D/'TASK.txt');j['active_peers']=['cmdrr-five-three-formal-sol-r4','shoe-pair-discrepancy-formal-sol-r4'];j['prelaunch_update']='Updated completedshoeR3-to-plannedR4 peer routing and Natendpoint/unpaid-audit scope before anybootstrap, reservationunchanged.';q.write_text(json.dumps(j,indent=2)+'\n')
assert all(sha(Path(s))==v for s,v in df.items())
ready={'utc':now,'shoe_lane':str(L),'shoe_frozen':len(frozen),'shoe_task_sha256':sha(L/'TASK.txt'),'discovery_lane':str(D),'discovery_task_sha256':sha(D/'TASK.txt'),'verified_old_manifest_files':len(files),'verified_old_frozen':395,'old_receipt_exit_counts':record['receipt_exit_counts'],'deep_audit_memory_failures':len(memory),'parent_integration':str(parent),'accepted_new':55,'credit':0,'other_active':'cmdrr-five-three-formal-sol-r4'}
save(ROOT/'shoe-r4-r436-ready.json',ready);print(json.dumps(ready))
