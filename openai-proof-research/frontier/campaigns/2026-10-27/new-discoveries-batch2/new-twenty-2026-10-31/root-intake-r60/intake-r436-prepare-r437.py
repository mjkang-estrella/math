import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r436';L=P/'expanded-corpus-r437'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==55 and not L.exists()
m=json.loads((A/'SHA256-MANIFEST.json').read_text());files=m['files'];assert all(sha(A/n)==v['sha256'] for n,v in files.items())
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==12 and all(sha(Path(s))==v for s,v in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==12 and not after['mismatches']
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];assert len(ids)==20 and sha(A/'reservation.json')==(A/'reservation.sha256').read_text().split()[0]
bindings=json.loads((A/'literal-bindings.json').read_text());assert len(bindings)==20;chunks={}
for row in bindings:
 q=Path(row['path'])
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert raw==row['raw'].encode() and raw.endswith(b'\n') and dg(raw)==row['raw_sha256']
 obj=json.loads(raw);assert obj['mathdb_id']==row['id']
 token=re.search(rb'"statement"\s*:\s*("(?:\\.|[^"\\])*")',raw).group(1)
 assert token==row['statement_token'].encode() and dg(token)==row['token_sha256']
 assert json.loads(token)==obj['statement']==row['decoded_statement'] and dg(obj['statement'].encode())==row['decoded_sha256']
assert {row['id'] for row in bindings}==set(ids)
original=(A/'original20.jsonl').read_bytes().splitlines(keepends=True);assert len(original)==20 and set(original)=={row['raw'].encode() for row in bindings}
gates=json.loads((A/'results.json').read_text());assert set(map(int,gates))==set(ids)
prev='0'*64;events=[]
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256']
assert sum(e['event']=='attempt' for e in events)==7 and sum(e['event']=='success' for e in events)==7
assert not any(e['event'] in ['unavailable','redirect'] for e in events)
rec=[]
for n,v in files.items():
 if n.endswith('.receipt.json'):
  j=json.loads((A/n).read_text());rec.append({'path':n,'sha256':v['sha256'],'exit':j.get('exit'),'killed':j.get('killed')})
terminal='seal-manifest.receipt.json';j=json.loads((A/terminal).read_text());rec.append({'path':terminal,'sha256':sha(A/terminal),'exit':j.get('exit'),'killed':j.get('killed'),'terminal':True})
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
for i in [1,2,3]:assert isinstance(json.loads((A/f'search-response{i}.json').read_text()),str)
parent=P/'expanded-corpus-r436-parent-integration.json'
record={'utc':now,'lane':str(A),'manifest_files_verified':len(files),'manifest_mismatches':[],'frozen_verified':12,'frozen_mismatches':[],'frozen_after':after,'literal_bindings_verified':ids,'raw_token_decoded_and_aggregate_bindings_verified':True,'all20_author_gates':gates,'guard_chain_verified':True,'guard_last_sha256':prev,'GET_hops':7,'successes':7,'redirects':0,'new_unavailable_artifacts':[],'search_calls':3,'search_querystrings':9,'empty_search_result':'Call2emptyretained,notretried;notnoveltyevidence','receipt_count':len(rec),'receipt_exit_counts':dict(collections.Counter(str(x['exit']) for x in rec)),'receipts':rec,'root_disposition':'No qualified survivor or formal dispatch.342217fullarbitrary-colorclassificationgap;343211profile-weightaggregationgapwithidentifiedunreadJLMSfinal;343592chain/cardinality-to-countabledownsetseparationgap. Partialidentities/subclasses/failed-shortcutcounterexamplesNOTtargetsolutions.','source_coverage':'All20literalsread; actualprimarybodiesonly3selectedroutes; other17unread. Latest/final/currentregistryproofbodiesunpaid. No theoremexclusionorworldwidenoveltyclaimfrommetadata.','history_limits':'707hashedallowlistedcompletedfiles,r99SHA-substringfalsematchremoved; neighboringIDs342367/347266/348101doNOTtransfersolutionsto342366/347268/381564. No oldcertificateaudit.','procedure':'Immutableownrunner/writer,explicitowncwd,hashchain/searchcounterpreserved; no deniedretrieval or backgroundreported. Sampling/native/writerlimitsretained; no universalprocessclaim.','credit':0,'accepted_new':55,'target_new':60,'previous_accepted':39,'root_execution':'Documentaryintegrity/orchestrationonly,no mathematical/Lean execution'}
save(parent,record)
den=json.loads((ROOT/'inherited-denials-r436.json').read_text());den['utc']=now
den['root_r436_outcome']='7successfulGETs,no newdenial.342217/343211/343592fullscopeproofsunpaid;343211specificJLMS10.1112/jlms.12484finalUNREADnotdenied,noclearance. Other17sourcebodiesunread. All inherited artifact-wide refusals continue.'
denpath=ROOT/'inherited-denials-r437.json';save(denpath,den)

# Execute the complete metadata-only preparation in an explicit namespace.
# It defines all its own selector/protection variables; no fragile partial resume.
source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();tail=source[source.index('# Metadata selector:'):];tail=tail[:tail.rfind('\nprint(')]
tail=tail.replace('selection-routing-r434.json','selection-routing-r437.json').replace('for num in range(421,434):','for num in range(421,437):')
tail=tail.replace('cmdrr-five-three-formal-sol-r3','cmdrr-five-three-formal-sol-r4').replace('shoe-pair-discrepancy-formal-sol-r2','shoe-pair-discrepancy-formal-sol-r4')
tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2','cactus-randic-ratio-source-review-sol-r1']:")
latest='''\nLATEST ROOT ROUTING:55/60beyond39accepted,94total;ONLYGPT-6.1Solhigh/defaultALLagents/nochildren. Activecmdrr-five-three-formal-sol-r4 andshoe-pair-discrepancy-formal-sol-r4fullyprotectedfromread/hash/glob/list/poll evenmetadata; rootexcludedIDs326555/324571andprimaryURLs1310.5240/1211.6486fromnew20usingretainedmetadata. Shoe324571actualPMFNatuniformSUP<=255/256<1strict/checker/fresh20module-replaygreen,NOTtechnicalPASS/accepted:genericcolortransport/finitezeroextensionandwholebodyoriginDAGauditunpaid(3memory-6failures),r4repairactive. CMDRR22production+auditpartial, centralidentities/cycle-sign/universalendpointunpaid,r4active;priorr3workspaceinventorymetadata-traversal/missingreapreceiptbreachretained,newrunnerowncwdguardnotwaiver. Rootauthorizedspecificcappedown-logdisplayandcorrectinstalledPDFmarkerpathr4;no general boundary waiver. Neither familymayberecounted. PriorCMDRR2013companion403/Galbraith-Holmes2012birthday404unreadlimits remain(allnewalternate deliveriesforbidden),boundedqualificationnotworldwidenovelty.\nCompletedr436all0:342217root-vectorboundaryidentity/binarymergesnotarbitrary-colorclassification;343211anti-monotoneprofilesubclass/weakpadding/permutationeventsdoNOTfullweightedprofilebound,actualJLMS10.1112/jlms.12484finalUNREADnotdenied;343592countabledownsetcriterionnotderivationfromchain/cardinalityhypotheses. Other17primarybodiesunread.7GETsuccess,3search9queries(call2emptyretained/no retry),12frozenintact. Historicalr99rawSHA-substringfalsematchnotprior;neighborIDs342367/347266/348101notdispositiontransferto342366/347268/381564. Match actualIDkeys/sourcefields, notdigitsinsidehashes.\nCompletedr435:352883actualpublicissue19720all-kweighteddescentproofexactzero;351851actualsourceTheorem4dual-signcorrectionzero.351165independentfull-literalGAP/numericalsourcecorollaryzero:actual2107.00071v2Theorems5.2/5.4+Lemma3.2 strongerhalf-diameterboundsdirectlygiveBOTHnumericalratiosviafullparameterfactorization;undefinedsymmetry/mixed2leaves-vs2pendantbridges/singletondomainnotauthenticatedfullrefutation,NOcredit/noformal/furtherretrievallane. Readallrelevantstrongerexistingstatements/proofsBEFOREbigproofinvestment; conjecturemayalreadyfollowfromanother theorem in samepaper. r434349307actualDing-Yan2608.15521jointcycleJfractionpublic,356364sourceowncycleinvariant/exceptioncorrection,354623ownsourcev3cochordalcounterexamples—allzero;3545712balancedspanningtreeaugmentationunpaid.\n323710coverratioordinary/current1206.6605v1PASS/provisionalcontent, actual2017JGTcompanion10.1002/jgt.22029final403ALLnewdeliveryunavailable=>PARKnoformal/retrievallane. Cachedv2Figure3signinconsistencyNOTattributedfinal/notusedwitness.323059fourK9interiord8ordinary-v1PASSbutactual2013Order10.1007/s11083-012-9253-5finalcookie-loopunavailable=>PARK.323064/323065scoringordinaryunqualifiedonefamily/source3.4adaptationobjection;323032actualpinnedupstream185packingcoveringcounterexamplepubliczero;323987actualLin1310.6726signedmultisetproofpubliczero.324245specificP-partitionCor3.4PIIS0097316519301177body403ALLnewdeliveryunavailable.323164/323165Chapoton2014final404ALLnewdeliveryunavailable;Su2017forkenumerationproofUNREADnotdenied,cached1203.1780notfinalequivalence. CurrentMathDB324571challenge-suffixrecordALLnewdeliveryunavailable,noguardledgerbackfill;cachedimmutableliteral/actualshoeoriginal-finalPDFdistinctallowedwherecopied.\n326886exactMa1506.05525v2T3.2fullparameterpublicproofzero,bodyread;Feng2019redirect-onlydenied.340110technicalfullLeanPASSbutrootEXCLUDEcompleteinverse-lemma/unit2cycle/cosetcollisionadaptation,noearlierexactprintedwitnessclaimed.337705hypergraphspecificclassicalproofunreadPARK;329292framefinal429PARK;332935graphsquarefinal/cactusrootunavailablePARK;334556finiteenergyPASSbutexactnorm/wcebridgeunpaid,QMC2014TLSallnewdeliverydenied. Everyinheriteddenialandallr39576acquisitionquarantinebinds. Rootintakes documentaryonly,notnewmathematicalproof. Sourcepublicsolutions/routinefullybridgedcorollaries/wording-domainendpointcorrectionsZERO. SpecificmatchingunreadtheoremHOLD;genericworldwideunknownnotautomaticveto;boundednonmatchnotworldwidenovelty. ReviewexactIDANDsourcefamilyhistoryBEFOREinvestment; actualprimarydefinition/theorem/proofbodyandscopebridgesrequiredforscientificclearance,neverabstract/head/snippet/openlabel/README/hashsubstring.\n'''
tail=re.sub(r"latest='''.*?'''",lambda _: 'latest='+repr(latest),tail,count=1,flags=re.S)
namespace=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+'#complete-metadata-r437','exec'),namespace)
t=(L/'TASK.txt').read_text()
for word in ['Resources fixed:','Deliver actual','frozen-after','receiptJSON','wholelane maximum3 actual calls9','cmdrr-five-three-formal-sol-r4','shoe-pair-discrepancy-formal-sol-r4']:assert word in t,word
f=json.loads((L/'frozen-inputs.json').read_text());assert len(f)==12 and all(sha(Path(s))==v for s,v in f.items());assert not (L/'bootstrap-receipt.json').exists()
ready={'utc':now,'new_discovery_lane':str(L),'ids':json.loads((L/'reservation.json').read_text())['ids'],'task_sha256':sha(L/'TASK.txt'),'intake_manifest_files':len(files),'intake_frozen':12,'intake_receipt_exit_counts':record['receipt_exit_counts'],'parent_integration':str(parent),'latest_denials':str(denpath),'accepted_new':55,'credit':0,'active_peers':['cmdrr-five-three-formal-sol-r4','shoe-pair-discrepancy-formal-sol-r4'],'root_role':'Documentaryintegrity/orchestrationonly'}
save(ROOT/'r437-ready.json',ready);print(json.dumps(ready))
