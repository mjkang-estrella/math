import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,shutil,ast
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
R=P/'cmdrr-five-three-formal-sol-r3';L=P/'cmdrr-five-three-formal-sol-r4'
BASE=P/'flat-balance-bridges-formal-pi-r5'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
assert not L.exists()
ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==55
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
m=json.loads((R/'SHA256-MANIFEST.json').read_text());files=m['sha256'];assert all(sha(R/n)==v for n,v in files.items())
frozen=json.loads((R/'frozen-inputs.json').read_text());assert all(sha(Path(s))==v for s,v in frozen.items())
after=json.loads((R/'frozen-after.json').read_text());assert after['count']==296 and not after['mismatches']
state=json.loads((R/'results/326555.json').read_text());replay=json.loads((R/'results/PARTIAL-REPLAY-R3.json').read_text());assert replay['empty_build_verified']
assert all(x['exit']==0 for x in replay['commands'])
for mod,s in replay['source_hashes_after_checkers'].items():assert sha(R/'src'/f'{mod}.lean')==s
for mod,s in replay['oleans'].items():assert sha(R/'extracted-r3/build'/f'{mod}.olean')==s
rec=[];latest={}
for n,s in files.items():
 if n.startswith('receipt/') and n.endswith('.json'):
  j=json.loads((R/n).read_text());row={'path':n,'sha256':s,'label':j.get('label'),'exit':j.get('exit'),'guard':j.get('guard'),'group_members_left':j.get('group_members_left')};rec.append(row)
  lab=j.get('label','')
  if lab.startswith('lean_') or lab.startswith('leanchecker_'):
   if lab not in latest or int(j.get('stamp',0))>latest[lab]['stamp']:latest[lab]=dict(row,stamp=int(j.get('stamp',0)))
for n in m['terminal_noncircular_self_exclusions']:
 if n.startswith('receipt/') and n.endswith('.json'):
  j=json.loads((R/n).read_text());rec.append({'path':n,'sha256':sha(R/n),'label':j.get('label'),'exit':j.get('exit'),'guard':j.get('guard'),'group_members_left':j.get('group_members_left'),'terminal':True})
for row in state['modules']:
 mod=row['module'];assert sha(R/'src'/f'{mod}.lean')==row['source_sha256'] and sha(R/'build'/f'{mod}.olean')==row['olean_sha256']
 info=row['latest_strict'];assert sha(R/info['path'])==info['sha256'] and info['exit']==0
 assert latest['lean_'+mod]['exit']==0 and latest['leanchecker_'+mod]['exit']==0
order=list(dict.fromkeys(x['module'] for x in replay['commands']))
assert len(order)==23 and len([n for n in order if not n.startswith('CMDRRAudit')])==22
parent=P/'cmdrr-five-three-formal-parent-integration-sol-r3.json'
record={'utc':now,'mathdb_id':326555,'reviewed_lane':str(R),'manifest_files_verified':len(files),'manifest_mismatches':[],'manifest_sha256':sha(R/'SHA256-MANIFEST.json'),'frozen_verified':len(frozen),'frozen_mismatches':[],'frozen_after':after,'receipt_count':len(rec),'receipt_exit_counts':dict(collections.Counter(str(x['exit']) for x in rec)),'receipts':rec,'latest_strict_checker_receipts':latest,'partial_replay':replay,'actual_state':state,'source_only_baseline_order':order,'production_modules':22,'auxiliary_audit_modules':1,'root_status':'VERIFIED_PARTIAL__PROCEDURAL_BREACH_UNRESOLVED__NO_ENDPOINT','root_disposition':'Continue ONLY source-only checked partial artifacts with historical process breach retained. No acceptance/credit or universal compliance PASS. Full endpoint/source-fidelity/deepbody audit/clean replay/controls/paper/independent review remain unpaid.','historical_process_breach':'Initial inventory omitted cwd and began recursive traversal at workspace root; protected-peer metadata traversal cannot be excluded, no protected proof body bytes reported read. Interrupted run has no normal receipt/reap evidence; observed tool session exit124 does not prove normal runner cleanup. All later completed receipt groups empty do not cure the missing historical evidence.','prospective_repair_not_waiver':'New immutable runner will chdir to its own absolute lane before any child dispatch; explicit workdir and known-file inventories mandated. This prevents recurrence and does not retroactively clear source-run breach. New full source-only replay and independent final audit/root process adjudication still required.','body_origin_limits':'Author315production declarations/5989reachable DAG nodes and four partial closures claimed with actual audit log; root only validates hashes/receipts, not independent mathematical or deep-body audit.','prior_limit':'Unread Berman-Smith2013body403, bounded prospective qualification only; no worldwide novelty or new retrieval.','accepted_new':55,'target_new':60,'previous_accepted':39,'credit':0,'root_execution':'Documentary integrity/orchestration and generic process-wrapper repair only; no math/Lean execution'}
save(parent,record)

L.mkdir();origins={}
def cp(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]={'path':str(src),'sha256':sha(src)}
for n in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh']:cp(BASE/n,n)
# Prevent recurrence of the observed cwd leak in this NEW lane only. Caps untouched.
runner=L/'runner.py';text=runner.read_text();anchor="    lane = os.path.dirname(os.path.abspath(__file__))\n";assert text.count(anchor)==1
before=sha(runner);runner.write_text(text.replace(anchor,anchor+"    os.chdir(lane)  # Root r4 guard: child commands always start in their own lane.\n",1))
save(L/'RUNNER-DELTA.json',{'reason':'Prevent workspace-root inventory traversal after missing tool workdir','old_generic_sha256':before,'new_sha256':sha(runner),'exact_change':'os.chdir(lane) immediately after resolving own runner directory and before dispatch; allcaps/trueexit/reaping/logging unchanged','scope':'New r4 lane only, never active or frozen old helpers','not_a_waiver':'Historical r3 breach remains unresolved/unaccepted'})
for n in ['src','build','audit','receipt','logs','tmp','cache','results','manuscript','output/pdf']:(L/n).mkdir(parents=True,exist_ok=True)
cp(R/'PINS.json','PINS.json');pins=json.loads((L/'PINS.json').read_text());assert sha(Path(pins['lean_bin']))==pins['lean_sha256'] and sha(Path(pins['leanchecker_bin']))==pins['leanchecker_sha256']
pack=Path(pins['packages_root']);bins=Path(pins['lean_bin']).parent
upstream=[str(pack/n/'.lake/build/lib/lean') for n in ['mathlib','batteries','aesop','Qq','proofwidgets','importGraph','LeanSearchClient','plausible']]
(L/'env.sh').write_text('#!/bin/bash\nset -eu\nLANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)\nLEAN_BIN='+str(bins)+'\nexport PATH="$LEAN_BIN:$PATH"\nexport LEAN_PATH="$LANE/build:'+':'.join(upstream)+'"\n')
for q in (R/'inputs').rglob('*'):
 if q.is_file():cp(q,'inputs/original/'+str(q.relative_to(R/'inputs')))
for n in ['SUMMARY.md','CHECKPOINT.md','results/326555.json','results/PARTIAL-REPLAY-R3.json','SHA256-MANIFEST.json']:
 cp(R/n,'inputs/previous/'+n)
for mod in order:
 cp(R/'src'/f'{mod}.lean',f'inputs/baseline-src/{mod}.lean');cp(R/'src'/f'{mod}.lean',f'src/{mod}.lean')
cp(parent,'inputs/ROOT-INTEGRATION.json');cp(ROOT/'inherited-denials-r435.json','inputs/INHERITED-DENIALS.json')
save(L/'INPUT-ORIGINS.json',origins)
tree=ast.parse((ROOT/'intake-shoe-cmdrr-and-prepare-formal.py').read_text())
common=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
detail='''CONTINUE CMDRR326555 fullNONEXISTENCE. Read current inputs/previous/CHECKPOINT.md and results/326555.json in FULL, rootintegration and originalindependentsource/ordinaryproof (under inputs/original nestedcopies) plus sourceDefinition1.2/canonicalmodel. Exact22production+AuditR3 coldcompile dependencyorder in ROOT-PREP/source-baseline-order aftermandatoryreads/pins; NOoldoleanscopied. Baselinepreflight explicitexceptionbeforeFIRSTNEWproofwrite; don'tspendturnredoingpaidorbit/normalizationtheory. FIRSTNEWproofoperation write actual occurrence-incidence identity module (e.g.CMDRRIncidenceSums.lean) then strictcheck BEFOREbroadAPIprobes. Use EXACTexistingSource, canonical0/1/2spouses3/4singles, rowdomains and A/B/z occurrencecounts in CMDRRZeroA; no newproxydefinitions or fieldsencodingidentities. Later diagnostics-guided APIreads allowed. Continue throughfullendpoint, notanotherhelper-onlysession.

PAID22baseline: literalunorderedsource/matching/scheduleoccurrences, counts22/11, T/U/Cgenuinepermutations C(Tx)=Ux; arbitraryrelabelling and explicitcanonicalFin5transport; uniqueother-singlemultiplicity; actualrestrictedrowpermutations; structural4pointorbit/spouserowfourcycles; complementary2+2directedrowdegree; 2cycleoccurrencesdistinct and count2exhaustion; actualA/B/zdefinitions and A=0 for single-man orientedfemale3->4->3two-cycle. Allsourcehashes/realgreenreceiptsinrootintegration, but NOTindependentfinalsourceacceptance. Canonicaltransportpaid, noSourceabsent; reverseequivalenceonlyprove if neededforfullsourcefaithfulness. Ifbaselinefidelitygaprequireschange, editONLYownworkingcopy, documentdiff/rebuild, frozenreferencebytesunchanged.

NOWPAY central actualdoublecount: sumactualspouserowinternaledgecounts overthree spousemen; countfemale-single45games2 partitionby0/1/2spousemen to get2+A-z; countthreefemaleH-pairgames withspouseavoidance to get3-B. Derive A+B=1+z using actualsourceoccurrences and bijections/incidences, allfinitecardinality/pairunordered/factors2 justified. No assertedauditcomment/ordinarylemma substitutedforproof.
Foranysingle-rowtwo-cycle, usepaidderivedsinglewomenrestriction/orientationsymmetry to connecttoalreadycompiledA=0. Itsremaining3womenorbitclosed bybijectionandno-fixedpoints; everyotherrowgamebothwomenH. Thetwo gamesagainstoppositesinglepartitionintoB andz, proveB+z=2. CombinewithA+B=1+z to2z=1contradiction(allNat/Intcastsjustified). Concludeall singlerows5cycles viaactualorbit/cardinalpartition, notassumedclassification.
ApplyENTIREincidence/eliminationtoSource.swap and explicitlyidentify swappedrowpermwithoriginalcolumnperm, so spousecolumns4cycles/singlecolumns5cycles. PaidSource.swap alone notthiscorrespondence. Prove signsofsupportedcycles/disjointrowandcolproducts ->signU=signC=-1 on22allowedcells; actualTfixedpointfreeinvolution11twoorbits ->signT=-1; CcomposedT=U ->signT=+1 contradiction. AssemblecanonicalnoSource and arbitrary5-elementmale/female/source-spousematching3 universalnegationExistsFiveThree viaactualcanonicaltransport. Sourcek=3spousepairs NOTrounds, noresolvability/extraLatinconstraints, noendpointconditionalonunpaididentity/cycle/signfacts. Noscheduleenumerationoruncheckedcertificate.

POSTENDPOINTcompletewholeenvironment/private/generatedbodyoriginDAG/exactclosureaudit, permitONLYpropext/Classical.choice/Quot.sound; actual315production/5989DAG/fourpartialclosurecountsfromr3donotreplacefinalendpointaudit. Substantivepositive/sourcecontrols andcleanisolatedsemanticnegativecontrols withtrueexpectedfail; fullALLsource-onlyEMPTYbuildreplay/checker/postcheckerhash; finishedpaperPDFallpagesvisualQA. Priorbody403limitation/no worldwidenoveltyclaim retained. Noindependentacceptance/credit/ledgerchange.

CRITICALPROCESS: r3initialinventoryranfromworkspace root, protectedmetadataaccesscannotbeexcluded, missingnormalcleanupreceipt. ThishistoricalPROCESSBREACHisretained, notwaivedbyhashes ornewwork. NewrootpreparedrunnerchdirsOWNabsoluteLane beforechilddispatch (RUNNER-DELTA.json),capsunchanged. Everyexec_command MUSTalso setworkdir=ABSOLUTEOWNLANE; use explicitabsolutehelpers, NOPath.cwd().rglob/wholeworkspacerecursion, no runner--help, no /dev/tty/tee displayworkaround. InventoryonlyknownownfilenamesorOWNabsolutePath.iterdir; no peers/parent trees evenmetadata. ExactrunnerCLI, sequentialjobs, boundedlogdisplaysinsideownrunner. No processsuccessclaimfortheinterruptedr3job; no bodybytesfromprotectedpeersreportedread,butmetadatauncertaintystays. Preserveallhistoricaldeviations/failuresinnewpaper/ledger, finalindependentreviewandrootprocessadjudicationrequired. ThisisresearchcontinuationauthorizationnotacceptanceorretroactiveproceduralPASS.'''
task='FullCMDRR326555continuationin '+str(L)+'. PROTECTEDACTIVEPEERS shoe-pair-discrepancy-formal-sol-r3,expanded-corpus-r435: NOread/hash/glob/list/poll evenmetadata.\n'+common.replace('LANE',str(L))+'\nSPECIFIC SCOPE:\n'+detail
(L/'TASK.txt').write_text(task)
save(L/'SOURCE-BASELINE-ORDER.json',{'order':order,'production_count':22,'auxiliary_count':1,'source':'PaidpartialR3strict+checker+source-onlyreplay','scope':'No endpoint/certificate/acceptance, freshownbuildmandatory'})
save(L/'ROOT-PREP.json',{'utc':now,'lane':str(L),'mathdb_id':326555,'model':'gpt-6.1-sol','provider':'codex','reasoning_effort':'high','service_tier':'default','children':False,'network':False,'accepted_new':55,'credit':0,'baseline_order':order,'no_old_oleans_copied':True,'process_breach_retained':True,'runner_cwd_guard':True,'root_role':'Documentary integration and generic process-wrapper repair only'})
frozen={str(q):sha(q) for q in R.rglob('*') if q.is_file()}
for q in (L/'inputs').rglob('*'):
 if q.is_file():frozen[str(q)]=sha(q)
for n in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh','PINS.json','env.sh','TASK.txt','INPUT-ORIGINS.json','ROOT-PREP.json','RUNNER-DELTA.json','SOURCE-BASELINE-ORDER.json']:frozen[str(L/n)]=sha(L/n)
assert all(sha(Path(s))==v for s,v in frozen.items());save(L/'frozen-inputs.json',frozen)
ready={'utc':now,'lane':str(L),'frozen_count':len(frozen),'task_sha256':sha(L/'TASK.txt'),'integration':str(parent),'verified_old_manifest_files':len(files),'verified_old_frozen':296,'old_receipt_exit_counts':record['receipt_exit_counts'],'runner_delta':str(L/'RUNNER-DELTA.json'),'accepted_new':55,'credit':0,'other_active_peers':['shoe-pair-discrepancy-formal-sol-r3','expanded-corpus-r435']}
save(ROOT/'cmdrr-r4-ready.json',ready);print(json.dumps(ready))
