import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,shutil,ast
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';R=P/'graph-wavelet-minimax-source-review-sol-r1';L=P/'graph-wavelet-minimax-primary-comparison-sol-r2'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not L.exists() and json.loads((P/'ledger.json').read_text())['accepted_new']==57
m=json.loads((R/'SHA256-MANIFEST.json').read_text());files=m['files'];assert len(files)==111 and all(sha(R/n)==v for n,v in files.items())
f=json.loads((R/'frozen-inputs.json').read_text());assert len(f)==171 and all(sha(Path(n))==v for n,v in f.items())
after=json.loads((R/'frozen-after.json').read_text());assert after['count']==171 and after['mismatches']==[]
assert not (R/'guard-ledger.jsonl').exists()
rec=[]
for n in [n for n in files if n.endswith('.receipt.json')]+[n for n in m['excluded_exact_paths'] if n.endswith('.receipt.json')]:
 j=json.loads((R/n).read_text());rec.append(dict(path=n,sha256=sha(R/n),exit=j.get('exit'),killed=j.get('killed')))
budget=json.loads((R/'search-budget.json').read_text());assert budget['calls_used']==2 and budget['queries_used']==6
failure=json.loads((R/'search/response1-capture-failure.json').read_text());assert not failure['full_actual_response_persisted_locally']
review=json.loads((R/'keyedreview.json').read_text())
parent=P/'graph-wavelet-minimax-source-parent-integration-sol-r1.json'
record=dict(utc=now,mathdb_id=332073,reviewed_lane=str(R),manifest_files_verified=len(files),manifest_sha256=sha(R/'SHA256-MANIFEST.json'),manifest_mismatches=[],frozen_verified=171,frozen_mismatches=[],frozen_after=after,receipts=rec,receipt_count=len(rec),receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in rec)),GET_hops=0,search_calls=2,querystrings=6,search1_capture_failure=failure,review=review,
 root_disposition='Independent ordinary/probability-free minimax refutation and original-v1 fidelity PASS retained. Full competitor with global mean closes source-basis objection; exactevenpartition legitimate under actualAlgorithm1/Conjecture1, not asserted optimal for ideal normalizedcutEq7. No formaldispatch/credit. Specific unread successor thesis Chapter4Algorithm6/Th28-29 and final-publication identity remain for focused primarycomparison.',
 process_adjudication='Missing full first-search response is a real retained archival breach. No reconstruction/backfill or oldcounterreset. Both2calls6queries consumed. Local proof/source reads and all171frozen unchanged give no basis for claiming mathematical corruption or blanket procedurePASS. New targeted distinct primarycomparison authorized with its own prospective budget; old failure never repaired by later work.',
 source_access='OwnGET0, no new denied work. ExactMathDB332073record inheritedchallengeunavailable persists; all latest union denials bind. Successor thesis/currentCV/publication not fetched/denied here. Search excerpt is navigation only, not authenticated body/date/author.',credit=0,accepted_new=57,target_new=60,previous_accepted=39,root_role='Documentary integrity/orchestration only, no mathematical/compiler execution')
save(parent,record)
L.mkdir();origins={}
def cp(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for n in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:cp(R/n,n)
cp(ROOT/'inherited-denials-r440.json','inherited-denials.json')
for q in (R/'inputs').rglob('*'):
 if q.is_file():cp(q,'inputs/'+str(q.relative_to(R/'inputs')))
for n in ['REVIEW.md','GAP.md','INDEPENDENT-PROOF.md','keyedreview.json','family-review.json','source-obligation-map.json','literal-validation.json','read-visual-access-inventory.json','resource-inventory.json','SHA256-MANIFEST.json','TERMINAL-EXCLUSIONS.json','search-budget.json','plans/search1.json','plans/search2.json','search/response1-capture-failure.json','search/response2.json','frozen-after.json']:
 cp(R/n,'inputs/independent-r1/'+n)
cp(parent,'inputs/ROOT-R1-INTEGRATION.json')
save(L/'INPUT-ORIGINS.json',origins)
save(L/'reservation.json',dict(ids=[332073],mathdb_id=332073,role='Focused successor thesis and final-publication/source-significance comparison',source_url='https://arxiv.org/abs/1512.05406',credit=0,accepted_new=57,target_new=60))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
tree=ast.parse((ROOT/'prepare-two-reviews-20261108.py').read_text());common=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
common=common.replace('Current55/60','Current57/60').replace('prior94total','prior96total').replace('Supplied55','Supplied57').replace('Inherited denial union r432','Inherited denial union r440')
detail='''Focused primary comparison for MathDB332073 after independent ordinary/source-v1 PASS. Active peers expanded-corpus-r440 andexpanded-corpus-r441 protectedfromread/hash/glob/list/poll evenmetadata. Personally GPT-6.1Solhigh/defaultONLY,nochildren,fallback,Lean/mathprograms/numerics. Rootcurrent57/60beyond39accepted96total. No implementation/creditdispatch.

Read copied r1 REVIEW/GAP/INDEPENDENT-PROOF, targetliteral/source original1512.05406and actualdefinitions/Conjecture1, saved authorresearch/literature evidence. Preserve ordinary strict4>2 minmaxPASS, true full competitor containingglobalmean, everyall-evenhierarchy>=3; idealEq7cutobjectiveNOTanAlgorithm1premiseverifiedbyr1. No need another broad proof reinvention. If newprimarydefinition changes scope, giveexactscopeandrepair/objection; keep original-v1 endpoint separate. Mathematicalsourcefamily57accepted+39priorcomparisonalreadyr1PASS, retainasboundedfindingsratherthanoldcertificateaudit. Onepossiblefamilyonly.

O1 SPECIFIC SUCCESSOR THESIS: source navigation title Exploiting Structure In Data: Sampling and Signal Processing on Graphs, attributed by r1 toRohanA.Varma, dates2019/2020conflict. MUSTauthenticate actualauthor/institution/date/titlefromprimary frontmatter/repository metadata, not assumethe r1attributioncorrect. TargetChapter4Algorithm6/Theorems28-29 andsurroundingoptimality/conjecturalparagraph/communitycaveat. Savedsearch2fullresponse hasan academia.edu mirror text excerpt; itisnavigationNOTauthenticatedprimarybody. Prefer actualofficialinstitutionalrepositorylinked thesisPDF (CMUKilthub/figshareoractualidentifiedprimaryhost), observedlinks only; no guessedfilename/seedlist/HTTPHEAD/APIcustomclient. An actualdocumentmetadataGET viafixedguard may be used if linkedpublicrepositoryservesJSON as its documentary entry point; noaccounts/forms/browser/credentialoperations. SourceidentitycouldturnoutSihengChenratherthanVarmaorchangeddate,resolvefromactualbody. ReadACTUAL theoremANDproof passages andmaterialfigures as needed, plus bibliography/sourcechaptercredit. Determine preservedconjecture/exactpublicresolution/correction/restrictionorboundednonmatch throughCOMPLETEbridge. Mere repeatedclaim or correctorthonormality doesnotproveglobalminimax. IfspecificapplicabletheorembodyunreadretainpreciseHOLD. No body available/failedrequest=>wholeartifactunavailableallnewalternatedeliveries, stopthatroute, noretries.

O2 FINALPUBLICATION/CORRECTIONS: sourcecached1512.05406v1record listsoneversion,noidentifiedjournal. SavedCVnavigation https://users.ece.cmu.edu/~sihengc/CV_siheng_chen.pdf (notpreviouslyGETdenied) lists changedauthorsS.Chen,T.Ji,R.Varma,A.Singh,J.Kovacevic andSignalrepresentationsongraphs:toolsandapplications as a plannedIEEETrans.SignalProc.submission. Authenticateactualbibliographicpublicationhistory/currentrevised/final/correction ifoneexistsusingactualprimarymetadata/bodyunderremainingbudget. Do NOTequateoldplannedsubmissionwithpublishedversionorforceuniversalnegativeproofthatnopaperexists. Afterboundedactualprimarycomparison, absenceofidentifiedfinalisadocumentedlimitnotautomaticgenericveto. Ifactualpublishedfinalidentifiedandmaterialbodyunread,itisa preciseHOLD. Cachedoriginalcannotbe refetched/reinterpretedbysearchsnippets; originalcurrentMathDBrecordchallengeunavailable, no API/cache/alternateURLfetchofthatrecord. Currentexactregistryproofbodyonlyifconcretematchingcounterclaimidentified; cached4headsareboundednavigationnotcompletetreeproofclearance. No newfullregistryrootGETneeded, no globalnoveltyclaim.

O3 SIGNIFICANCE/priorbridge: completecomparisonofthesis/sourceownunequalcommunityparagraphwithstrictminimaxrefutation. It discussesfavorableunequalcutsbutstillassertsevenworst-caseoptimality; do thoseactualprimaryproofsprovidePCG(1)classification+fullcompetitorworstsupport+strictWgapalready? IfYEScompleteadaptation/publicsolutionZEROcreditwithstrongestcontrarycase. IfNO, preserveprospective substantivequalificationwithinboundedreview; standardHaar/Helmert/cliques/shortnessnotautomaticroutineexclusion. Noexactearlierwitnessclaimwithoutsource. Smallparameter/counterexamplecountsonefulluniversalrefutation,notparameterrecount. Distinguish ordinaryPASS,original/finalfidelity,prior/novelty/significance/family/process/formal/acceptance separately. A sourcecorrection/missingmandatorybasiscondition ZEROcredit ratherthannewtheorem. Rootonlyscientificqualificationandformalrouting,notyours.

RESOURCE/ACCESS: this NEWfocusedtask has max8TOTALactualGET-hops/per332073,2nativeSEARCHcalls6queries. It does NOTreset/repairoldr1counter2calls6queries ormissingsearch1response. Use different focused identity/primary-source questions, not rerunoldbroadqueries toreplace lostresponse. PRECHARGEeachactualnativequery/callandPERSISTFULLactualresultimmediatelybeforeanysubsequentwork; neverprintwithoutkeepingreturnedvalue. FullJSON-string savedislegitimate. Nohistoricalbackfill orinventedoldresponse. Retainr1ProcedureFAILandnetworkstopasoldscope; onlynewexplicitprospectiveworkauthorized. Exactoldplans,response2andcapturefailurearecopied. Include-site/author/title focusedqueries; exclude-site:mathdb.com toavoidaccidentalrecorddelivery; ifunsoliciteddeniedsourceexcerpthitquarantineunused,no followup. GETsolefixedsource_get_guard under exactrun.py, one observedmanuallyselectedplanwithroutes332073,newdestination,identity/purpose. Everyredirectprecharged; noalternate delivery/TLS/cookie/HTTPupgrade workaroundafterfail. LatestunionincludesfinalJNTlattice403,Mathematika403,Ye1999blockedHTTP,MathDB327053/332073challenge andalloldrefusals/r395quarantine. Distinctactualthesis/CVnotdeniedbythose. Stopnetworkandrecordonpolicy/budgetbreach, nohelper/ledgeredits. Allfrozeninputs/helperhashesunchanged.

DELIVER REVIEW.md, IDkeyedreview.json withO1/O2/O3PASS/HOLD/EXCLUDEprecisebridges,theactualprimaryidentity/date/bodyproofcomparison,strongestobjections+contraryassessment. Source/read/figure/access/search/resourceinventories,everyfullresponseplanandguardoutcome/failuretrueexit,actualmanifest withcompletedreceiptJSONs/exactterminalselfexclusions,mandatoryfrozenafter. Ifallscientificgatespassprovidefull-literalDORMANTLeanbrief usingimprovedmeancompetitorandtypedsourcehierarchy/operator/allrealconstraints, noformalexecution/dispatch. Only pinsLean4.34.1/mathlibd13f23b...,axiomtriolaterpipeline. No acceptance/selfcredit;57/60unchanged. Completefocusedprimaryworkpersonally,oldfailuresnotrepairedbynewPASS.
'''
task='Focused independent primary comparison332073 in '+str(L)+'\n'+common.replace('LANE',str(L)).replace('TARGET','332073')+'\nSPECIFIC OBLIGATIONS\n'+detail
(L/'TASK.txt').write_text(task)
bind={str(R/n):v for n,v in files.items()};bind[str(R/'SHA256-MANIFEST.json')]=sha(R/'SHA256-MANIFEST.json')
for n in m['excluded_exact_paths']:bind[str(R/n)]=sha(R/n)
for q in L.rglob('*'):
 if q.is_file() and q.name!='search-budget.json':bind[str(q)]=sha(q)
save(L/'frozen-inputs.json',bind);save(L/'ROOT-PREP.json',dict(utc=now,lane=str(L),target=332073,model='gpt-6.1-sol',reasoning='high',service='default',frozen=len(bind),protected_peers=['expanded-corpus-r440','expanded-corpus-r441'],credit=0,campaign=57,budget=dict(GET_hops=8,search_calls=2,queries=6)))
assert all(sha(Path(n))==v for n,v in bind.items())
save(ROOT/'wavelet-primary-r2-ready.json',dict(utc=now,lane=str(L),task_sha256=sha(L/'TASK.txt'),frozen=len(bind),old_manifest_verified=len(files),old_frozen_verified=171,credit=0))
print(json.dumps(dict(lane=str(L),old_files=len(files),old_frozen=171,receipts=len(rec),new_frozen=len(bind),credit=0)))
