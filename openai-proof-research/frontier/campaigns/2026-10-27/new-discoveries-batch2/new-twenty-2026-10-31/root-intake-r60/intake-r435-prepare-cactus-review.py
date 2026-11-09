import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,shutil,ast
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
A=P/'expanded-corpus-r435';L=P/'cactus-randic-ratio-source-review-sol-r1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
assert not L.exists();assert json.loads((P/'ledger.json').read_text())['accepted_new']==55
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
m=json.loads((A/'SHA256-MANIFEST.json').read_text());files=m['files'];assert all(sha(A/n)==v['sha256'] for n,v in files.items())
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==12 and all(sha(Path(s))==v for s,v in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==12 and not after['mismatches']
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];assert len(ids)==20 and len(set(ids))==20
assert sha(A/'reservation.json')==(A/'reservation.sha256').read_text().split()[0]
prov=json.loads((A/'literal-provenance.json').read_text());assert set(map(int,prov))==set(ids);chunks={}
for sid,row in prov.items():
 q=Path(row['chunk'])
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line_one_based']-1]
 assert raw==row['raw_line'].encode() and raw.endswith(b'\n') and dg(raw)==row['raw_sha256']
 obj=json.loads(raw);assert obj['mathdb_id']==int(sid)
 token=re.search(rb'"statement"\s*:\s*("(?:\\.|[^"\\])*")',raw).group(1)
 assert token==row['statement_token'].encode() and dg(token)==row['token_sha256']
 assert json.loads(token)==obj['statement']==row['statement'] and dg(obj['statement'].encode())==row['statement_sha256']
gates=json.loads((A/'results.json').read_text());assert set(map(int,gates))==set(ids)
prev='0'*64;events=[]
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256']
assert sum(e['event']=='attempt' for e in events)==11 and sum(e['event']=='success' for e in events)==11
assert not any(e['event']=='unavailable' for e in events)
rec=[]
for n,v in files.items():
 if n.endswith('.receipt.json'):
  j=json.loads((A/n).read_text());rec.append({'path':n,'sha256':v['sha256'],'exit':j.get('exit'),'killed':j.get('killed')})
terminal='handoff_manifest.receipt.json';j=json.loads((A/terminal).read_text());rec.append({'path':terminal,'sha256':sha(A/terminal),'exit':j.get('exit'),'killed':j.get('killed'),'terminal':True})
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
for i in [1,2,3]:assert isinstance(json.loads((A/f'search-response-{i}.json').read_text()),str)
parent=P/'expanded-corpus-r435-parent-integration.json'
record={'utc':now,'lane':str(A),'manifest_files_verified':len(files),'manifest_mismatches':[],'frozen_verified':12,'frozen_mismatches':[],'frozen_after':after,'literal_bindings_verified':ids,'raw_token_decoded_bindings_verified':True,'all20_author_gates':gates,'guard_chain_verified':True,'guard_last_sha256':prev,'GET_hops':11,'successes':11,'unavailable':0,'search_calls':3,'search_querystrings':9,'full_responses':['search-response-1.json','search-response-2.json','search-response-3.json'],'receipt_count':len(rec),'receipt_exit_counts':dict(collections.Counter(str(x['exit']) for x in rec)),'receipts':rec,'root_disposition':'No qualified survivor/credit.352883actualpublicissue19720all-kweighteddescentproofexclusion;351851completeactualsourceTheorem4sign-correctionbridgezero.351165bothinequalitiesordinaryproposal, fullliteralequality/source/prior/significanceunpaid; authorize independent full-scope review/repair only, no formal dispatch.','cactus_scope_limit':'Nontrivial bridge-free and mixed k>0,b>0 ranges, leaves/tree-skeleton transitions and constants covered by proposed proof; longitudinal symmetry definition and mixed equality remain source-fidelity gaps. No partial/numerical inequality alone counts.','procedural_limits':'Heterogeneous denial-record schema caused registry_inventoryexit1 after partialinventorywrite; corrected in distinct savedreceipt, no failednetwork/no retry. Material truncated reads recovered. Figures uninspected, native/writer/sampling peaks unavailable; no blanket universal compliance claim.','credit':0,'accepted_new':55,'target_new':60,'previous_accepted':39,'root_execution':'Documentary integrity/orchestration only; no mathematical programs or Lean execution'}
save(parent,record)
den=json.loads((ROOT/'inherited-denials-r435.json').read_text());den['utc']=now;den['root_r435_intake']='11successfulGETs,no newdeniedartifact; all prior artifact-wide denials retained. Cactus351165independentfullscope/equalityreviewauthorized,numericalsubsetnotcredited.'
denpath=ROOT/'inherited-denials-r435-intake.json';save(denpath,den)

tree=ast.parse((ROOT/'prepare-two-reviews-20261108.py').read_text())
common=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
common=common.replace('Inherited denial union r432','Inherited latest denial union r435-intake')
L.mkdir();origins={};base=P/'expanded-corpus-r420'
def cp(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]={'path':str(src),'sha256':sha(src)}
for n in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:cp(base/n,n)
cp(denpath,'inherited-denials.json')
for n in ['ACTUALBRIEF.md','FULLCANDIDATE.md','SUSTAINED-ORDINARY-ROUTES.md','DORMANT-SOL-FORMAL-PLAN.md','literal-provenance.json','results.json','ID-source-reconciliation.json','historical-reconciliation.json','history-read-inventory.json','access-inventory.json','read-inventory.json','resource-inventory.json','registry-inventory.json','SHA256-MANIFEST.json','search-response-1.json','search-response-2.json','search-response-3.json']:
 cp(A/n,'inputs/'+n)
for n in ['cactus.pdf','cactus.txt','cactus-record.html','cactus-companion.pdf','cactus-companion.txt','registry-openai.html','registry-leanpool.html','registry-tau.html','registry-deepmind.html']:
 cp(A/'sources'/n,'inputs/sources/'+n)
literal=prov['351165']['raw_line'].encode();q=L/'inputs/literal351165.jsonl';q.write_bytes(literal);origins['inputs/literal351165.jsonl']={'path':str(A/'literal-provenance.json'),'provenance_sha256':sha(A/'literal-provenance.json'),'sha256':dg(literal),'extraction':'Exact unchanged complete newline JSONL object from verified corpus binding'}
cp(ROOT/'accepted55-path-review-context.json','inputs/accepted55-routing.json')
cp(P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json','inputs/prior39-routing.json')
cp(parent,'inputs/ROOT-AUTHOR-INTEGRATION.json')
save(L/'INPUT-ORIGINS.json',origins)
save(L/'reservation.json',{'ids':[351165],'role':'Independent full ordinary proof/source/equality/prior/significance review and gap repair; no formal execution','accepted_new':55,'target_new':60,'credit':0})
rs=sha(L/'reservation.json');(L/'reservation.sha256').write_text(rs+'  reservation.json\n')
save(L/'search-budget.json',{'calls_used':0,'queries_used':0,'maximum_calls':2,'maximum_queries':6,'charged_before_call':True})
detail='''FULL literal MathDB351165 Sharper Randic-index/diameter cactus conjecture, INCLUDING equality clauses; no subset/new nearbyproblem credit. Author ordinary proof is a PROPOSAL, not a lemma. Independently inspect ALL hypotheses and reconstruct/repair both inequalities and exact equality or produce precise GAP/zero-credit correction classification. No mathematicalprograms/numericchecks/enumeration/solver/Lean. Sourceactual2107.00071v2Conjecture1.6 andmaterialdefinitions/proofs/FIGURES; later2309.11613v1Section6alreadycached. Establish nontrivial cactus range, connected finite SIMPLE unweighted assumptions, k/b/n/d andR convention, block-cut-tree vs block-tree terminology. Do not silently addk>=1 or d>0 if source/full literal does not imply it; isolate standing-domain issue explicitly. ExactsourcePDFcurrentrecordcopied; no refetch. Materialfigures NOTpreviouslyvisuallyinspected: use PDFskill via runner (explicit externalinstructionpath exception), renderOWNcopiedPDF, actuallyviewmaterialfigure/textpages, stateprecisereaddepth. DirectOWNrenderimage displayallowedasUIevidence, notsampledtelemetry. NoPDFauthoringrequested.

ORDINARY AUDIT: proposed q=3-2sqrt2,a=1+q,C=6-4/sqrt3-4sqrt(2/3), N=n+k+b-1=sumcyclelengths+2b,A=n-q(k-1)-delta,B=N-A,delta=Cifb>0else0; constantproof0<C<1/2<a<3/2 and6w23<q. Verify d<=N/2, A>0,2B<N, connecteddegree assumptions andsumdegreesdefect2R=n-sumw. Localpendant/cycleadditionestimates usingS=sumneighbor1/sqrt(deg)<=v (workswithleaves), positive DeltaR andcycleDeltaR>(s-2)/2. FixeddiameterF=A/N mayINCREASE undercycleaddition; check exact(sB-aN)/(N(N+s)) andstrictdominationbyDeltaR usingd<=N/2/B<N/2 inallcases. Firstpendantchangesdelta, paytransition. Diametralfull-block skeletonisometriccontainsdiametralpair; successivefull-blockgrowth reallypreservesdiameter andcoversallcacti. Cyclicchainsdefectcharges:cycle-cyclearticulation4w24=q, bridgerun6w23<q, twoexternalarms<=C; adjacentarticulations splittinginequalityorientation. Tree-onlyskeletoncase andfirst-cycletransition afterpendantgrowth,mindd2/k1/oddcycles/b0/b1allrange endpoints. Author claimsproofclosesbothnumericalineq universally; challengeconstants/signs/cyclelength/bookkeeping/strictnessandderivepersonally, notfromsymboliccomments alone.

EQUALITY/FIDELITY essential: literal says equality IF BC-tree path and longitudinally symmetric; mixedaddstwoleaves. Source text reportedly lacks a precise longitudinal-symmetrydefinition and proofrequiresEXACTLYtwo bridges,bothpendants. Inspectmaterialfigures/captions/definitionselsewhere: longitudinal symmetry might encode antipodalattachment/even-cycleconditions. Do not invent a favorable definition from intuition. Author's4-cycleoppositearmslength2 hasreflection/twoleaves/BCpath butstrictdefect<C; determinewhetheritactuallysatisfies sourcecondition, doNOTclaimliteralrefutationwithoutauthenticatedmeaning. Couldresolve sourcefaithfulnessbyspecifiedprecisepredicate onlyifactualsourcejustifiesit. A source sign/domain/equality typo correction earnsZEROcredit; bothinequalitiesalonecannotcountasfullcompositeliteral. If literal is onlyrefutable duealreadyprovedsourceequalityexception, supplyCOMPLETEbridge andstrongestcontrarycase; no smallnessshortcut. If equalitycanbeproved in source's exactscope, closebothdirections actually demanded (literalIF vsIFF distinguish),allstrictnessconditionsanddegeneratecases.

Currentprimaryqualification: authoractualv2recordshowsv2,nojournalreferencefound; obtainONLYnotcachedexactprimaryfinal/correction/history ifindependentlyidentified underbudget, actualbodybeforeassertingfinalequivalence. Later2309.11613radius/additivediameterproofsnot automaticallyratio. SourceCor4.5/Theorem4.6 chainbasesandLemma2.7 blockincrementproofs: assessCOMPLETEroutineadaptationbridge toallcacti includingmixedleaves/tree-skeleton/target-changingcyclecase, withstrongestcontrarysignificancecase. Familiar tools/shortproof alone notroutine, butactualexistingtheorems+fullypaidnewreductionmayexcludesubstantivecredit. No currentapplicable exactprioridentifiedyet; targetedactualprimary/regproofcounterpartsearchboundedmax2actualcalls6querystrings/max8guardedGEThopsTOTAL/perID. Rootheads/openlabels/snippetsnotproof/novelty. SpecificmatchingunreadtheoremHOLDvs genericworldwideunknownnotautomaticveto. No alternate deliveryofdeniedartifacts, no cachedrefetch/broadhistoryseed. Includeallknownr435newexclusionsonlyasboundedhistory, no externalpathfollowing.

Compare55fullaccepted+39prior scopesbeforeinvestment, no oldcertificateaudit; onefamilymax. Deliver fullindependentPROOFand/orpreciseGAP, exactsource/equalitymap, separateallgates/keyedreview/strongestobjections/source-read/figure/access/search/resourceinventories/SHAmanifestALLcompletedreceiptJSON/frozenafterwithnamedterminalexclusions. ProspectiveallgatesPASS mayjustifyDORMANTfullliteralLeanplanonly,nodispatch. Noqualifyingfullsolutionifmainliteralclauseunpaid. Noacceptance/credit;55/60beyond39unchanged. Preservehistoricalauthorfailures/limitsandownfailures, no blanketprocessclaim.'''
task='IndependentFULLscope351165review in '+str(L)+'. PROTECTEDACTIVEPEERS cmdrr-five-three-formal-sol-r4,shoe-pair-discrepancy-formal-sol-r3: NOread/hash/glob/list/poll evenmetadata. ReservationSHA256 '+rs+'.\n'+common.replace('LANE',str(L)).replace('TARGET','351165')+'\nSPECIFIC SCOPE:\n'+detail
(L/'TASK.txt').write_text(task)
frozen={str(q):sha(q) for q in A.rglob('*') if q.is_file()}
for q in (L/'inputs').rglob('*'):
 if q.is_file():frozen[str(q)]=sha(q)
for n in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','inherited-denials.json','INPUT-ORIGINS.json','reservation.json','reservation.sha256','TASK.txt']:frozen[str(L/n)]=sha(L/n)
assert all(sha(Path(s))==v for s,v in frozen.items());save(L/'frozen-inputs.json',frozen)
ready={'utc':now,'lane':str(L),'target':351165,'frozen_count':len(frozen),'reservation_sha256':rs,'task_sha256':sha(L/'TASK.txt'),'model':'gpt-6.1-sol','reasoning_effort':'high','service_tier':'default','children':False,'accepted_new':55,'credit':0,'intake_manifest_files':len(files),'intake_frozen':12,'intake_receipt_exit_counts':record['receipt_exit_counts'],'latest_denials':str(denpath),'other_active_peers':['cmdrr-five-three-formal-sol-r4','shoe-pair-discrepancy-formal-sol-r3'],'root_role':'Documentaryintegrity/orchestrationonly'}
save(L/'ROOT-PREP.json',ready);save(ROOT/'cactus-randic-review-ready.json',ready);print(json.dumps(ready))
