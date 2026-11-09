import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil,base64,ast
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r439';W=P/'graph-wavelet-minimax-source-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==57 and not W.exists()
m=json.loads((A/'SHA256-MANIFEST.json').read_text());files={n:({'sha256':v} if isinstance(v,str) else v) for n,v in m['files'].items()};assert len(files)==129 and all(sha(A/n)==v['sha256'] for n,v in files.items())
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==12 and all(sha(Path(n))==v for n,v in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==12 and after['mismatches']==[]
bindings=json.loads((A/'literal-bindings.json').read_text());res=json.loads((A/'reservation.json').read_text());ids=res['ids'];assert len(bindings)==len(ids)==20
chunks={};raws={}
for row in bindings:
 q=Path(row['chunk'])
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];raw=base64.b64decode(row['raw_b64']);assert h==row['chunk_sha256'] and lines[row['line']-1]==raw and dg(raw)==row['raw_sha256'] and row['newline'] and raw.endswith(b'\n')
 obj=json.loads(raw);assert obj['mathdb_id']==row['id'] and obj['statement']==row['statement'] and dg(obj['statement'].encode())==row['statement_utf8_sha256']
 tok=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1];assert tok==base64.b64decode(row['statement_token_b64']) and dg(tok)==row['statement_token_sha256'];raws[row['id']]=raw
assert set(raws)==set(ids) and set((A/'original-twenty.jsonl').read_bytes().splitlines(keepends=True))==set(raws.values())
gates=json.loads((A/'results.json').read_text());assert set(map(int,gates))==set(ids)
prev='0'*64;events=[]
for i,b in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 j=json.loads(b);assert j['seq']==i and j['previous']==prev;prev=dg(b);events.append(j)
 if j['event']=='success':assert sha(A/j['destination'])==j['sha256']
assert sum(j['event']=='attempt' for j in events)==14 and sum(j['event']=='success' for j in events)==13 and sum(j['event']=='unavailable' for j in events)==1
manual=json.loads((A/'manual-access-classification.json').read_text());assert len(manual['new_unavailable'])==2 and manual['network_stopped_after_challenge_discovery'] and manual['guard_history_unchanged']
for row in manual['new_unavailable']:
 assert sha(A/row['path'])==row['sha256'] and row['challenge_suffix']
rec=[]
for n in [n for n in files if n.endswith('.receipt.json')]+[n for n in m['terminal_noncircular_self_exclusions'] if n.endswith('.receipt.json')]:
 j=json.loads((A/n).read_text());rec.append(dict(path=n,sha256=sha(A/n),exit=j.get('exit'),killed=j.get('killed')))
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
parent=P/'expanded-corpus-r439-parent-integration.json'
save(parent,dict(utc=now,lane=str(A),manifest_files_verified=len(files),manifest_mismatches=[],frozen_verified=12,frozen_mismatches=[],frozen_after=after,literal_bindings_verified=ids,raw_token_decoded_and_aggregate=True,guard_chain_verified=True,guard_tail_sha256=prev,GET_hops=14,transport_successes=13,manual_unavailable=manual,search_calls=3,queries=9,receipts=rec,receipt_count=len(rec),receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in rec)),root_disposition='No qualified survivor or credit.327053ordinary lattice shell refutation proposal PARKED actualJNTfinal403;332073ordinarygraph-waveletminimaxproposal retained for independent proof/source/prior/significance review using cachedliteral and actualprimarysource, no formaldispatch.330708crosscutfibercancellationgap remains. Other17primarybodiesunread; no theorem/novelty clearance from current-record SSR challenge text.',root_role='Documentary integrity/orchestration only, no mathematical programs/compiler execution',credit=0,accepted_new_now=57,target_new=60,previous_accepted=39))
den=json.loads((ROOT/'inherited-denials-r439.json').read_text());den['utc']=now
bad=next(j for j in events if j['event']=='unavailable');den['blocked_keys']=sorted(set(den['blocked_keys']+[bad['url_key']]))
den['blocked_artifacts']=sorted(set(den['blocked_artifacts']+['10.1016/j.jnt.2014.02.015','1401.2891']))
den['records'].append(dict(url=bad['url'],reason=dict(status=403,artifact='Coulangeon-Lazzarini JNT141(2014)288-315 DOI10.1016/j.jnt.2014.02.015 PII S0022314X14001012 original1401.2891',restriction='Whole identified work unavailable across all NEW alternatehosts/queries/versions/cache/mirror/arxiv/author deliveries. Alreadycachedoriginal+distinctthesis only whereexplicitlycopied; no finalequivalence.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'))))
for row in manual['new_unavailable']:
 ev=next(j for j in events if j['event']=='success' and j['destination']==row['path']);u=ev['url'];from urllib.parse import urlsplit,unquote
 key=urlsplit(u).hostname.lower()+unquote(urlsplit(u).path).rstrip('/');den['blocked_keys']=sorted(set(den['blocked_keys']+[key]))
 den['records'].append(dict(url=u,reason=dict(artifact='Exact MathDB current record '+row['path'],status='transport200 challenge-suffix',restriction='Scientifically unavailable entire exact-record delivery acrossalternatehosts/query/cache/API/body routes. Do not execute challenge script or retry; original guard success history preserved, no backfill.'),evidence=dict(path=str(A/row['path']),sha256=row['sha256'],classification=str(A/'manual-access-classification.json'))))
den['root_r439_scope']='327053ordinaryproposalPARKED finalJNT10.1016/j.jnt.2014.02.015/1401.2891ALLnewbodydeliveryunavailableafter403. ExactcurrentMathDB327053/332073recordchallenge-suffixunavailable,transport200historynotrewritten. Target332073actual1512.05406cachedsource independentlyreviewable; unrelatedsuccessorworknotautomaticallydenied,butcannotindirectlyrecoverdeniedrecord/work.14hops13transportpayloads(2challenges),3search9queries,12frozenintact,0credit.'
denpath=ROOT/'inherited-denials-r440.json';save(denpath,den)
# Trusted current statement scopes, no prior certificate reads.
context=json.loads((ROOT/'accepted55-path-review-context.json').read_text());assert len(context['records'])==55
context['records'] += [json.loads((P/n).read_text()) for n in ['shoe-discrepancy-acceptance.json','cmdrr-five-three-acceptance.json']]
context['accepted_count']=57;context['utc']=now;context['kind']='Trusted57accepted statement scopes,39prior separately; metadata only';save(ROOT/'accepted57-review-context.json',context)

# Focused independent mathematical/source qualification of the wavelet proposal.
W.mkdir();origins={}
def cp(src,rel):
 dst=W/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for n in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:cp(A/n,n)
cp(denpath,'inherited-denials.json')
for n in ['ACTUALBRIEF.md','FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','literal-bindings.json','original-twenty.jsonl','results.json','source-resource-inventory.json','read-inventory.json','prior-reconciliation.json','manual-access-classification.json','SHA256-MANIFEST.json','search-response-1.json','search-response-2.json','search-response-3.json','guard-ledger.jsonl']:
 cp(A/n,'inputs/author/'+n)
for n in ['wavelet.pdf','wavelet.txt','wavelet-record.html','registry-openai.html','registry-leanpool.html','registry-tauceti.html','registry-deepmind.html']:
 cp(A/'sources'/n,'inputs/sources/'+n)
cp(ROOT/'accepted57-review-context.json','inputs/accepted57-routing.json');cp(P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json','inputs/prior39-routing.json');cp(parent,'inputs/ROOT-AUTHOR-INTEGRATION.json')
(W/'inputs/literal332073.jsonl').write_bytes(raws[332073]);save(W/'inputs/332073-gates.json',gates['332073']);save(W/'INPUT-ORIGINS.json',origins)
save(W/'reservation.json',dict(ids=[332073],mathdb_id=332073,source_url='https://arxiv.org/abs/1512.05406',role='Independent full graph-wavelet minimax proof, exact source and significance qualification',credit=0,accepted_new=57,target_new=60))
(W/'reservation.sha256').write_text(sha(W/'reservation.json')+'  reservation.json\n');save(W/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
tree=ast.parse((ROOT/'prepare-two-reviews-20261108.py').read_text());common=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
common=common.replace('Current55/60','Current57/60').replace('prior94total','prior96total').replace('Supplied55','Supplied57').replace('Inherited denial union r432','Inherited denial union r440')
detail='''Independent full ordinary proof, literal/source, prior/final and significance review of MathDB332073 local-set piecewise-constant graph wavelet orthonormal minimax conjecture. Protected plannedpeers expanded-corpus-r440 andexpanded-corpus-r441; no read/hash/glob/list/poll evenmetadata. Nochildren/fallback/formalexecution. Root57/60beyond39accepted96total; two new accepted scopes shoe324571 andCMDRR326555 are in trusted57scopefile, not new certificateaudit. One possible family only; no optimalK/graphparameter/helper credits.

Read exact copied literal/raw/source/provenance and actual1512.05406v1 definitions9/10, Algorithm1, Theorems8/9 proofs, Conjecture1 and full following community caveat. PROPOSAL: connected simple unweighted K3 joined by ONE bridge toK5, K1. All admissible real signals with at most1inconsistent edge are exactlyspan{1_A,1_B}. A complete competing orthonormal basis containing normalized clique indicators and Helmertcontrasts hasworstsupport2. A perfectlyevenconnectedhierarchy4|4,2|2,... gives1_A fourexplicit nonzero coefficients inW. Root4|4set{1,2,3,4}|{5,6,7,8},left{1,2}|{3,4},right{5,6}|{7,8} andpairs are allconnected. Needindependentlyverify graphdifferenceoperatornorm/support definition countsedgeorientation once vsboth, K=1admissibility, source evenpartition definition/algorithmselection/edgecutoptimality constraints, orthonormalbasisclass whetherglobalconstantcolumnmandatory forcompetitors orbasisactuallyN-1zero-mean, every allowed orthonormal basis quantified, fixedtie-break/partitionchoice and exactWconstruction. Do not assume mereequalcardinality makesa sourcelegalpartition ifthereis an additionalcutobjective. Pay allreal/singleton/constant/zerocases, fullbasiscompletion, exactcoefficientnorms, supportmaxwitness andfullminimaxcomparison. No numerical tests/enumeration/Python/CAS. Fullordinaryproofpersonally or exactGAP/repair. Sourceowncaveat maygivecompleteknownsolution; ifso supplyfullbridgeandzero-creditexclusion ratherthanclaim novelty fromconjecturelabel.

Strongestscopeobjections: mandatorymeanbasisvector constraint could invalidate proposedF; sourceKconstraint/cutnormalization coulddoublecountbridge; evenpartitionselectionmaybemorethanbalancedsize; conjecture's argmin/equality/zero-mean conventionsmaydiffer. Review actualtypeddefinition andall standinghypotheses before accepting witness. The robustallperfectlyevenroot argument is supportingmechanism, explicitlegalhierarchyalone suffices if quantified source allowsit. A wrongglobalbasisproxy or upperboundcomparison alone isnotrefutation.

Scientificqualification: cachedarxivrecordlistsv1, nojournref identified; identify actual final/publication/corrections through targetedboundedprimaryevidence, not globalabsencefrommetadata. A2019thesis search excerpt repeatsheuristic: locate/authenticate ACTUALprimary relevanttheorem+proof ratherthansnippet. TargetcurrentMathDBrecord332073haschallenge suffix andisartifact-wideunavailable; no record/API/cache/alternateURLdelivery/retry; cachedcorpusliteral remains target. ItsvisibleSSRopen/zero solutioncountsarenotnoveltyevidence. Lattice327053entirefinalJNTwork/1401.2891denied too, not thiswaveletpaper, do notindirectrecoverit. All other latestuniondenials bind. Source1512.05406alreadycachednofetch. Targetednewdistinctfinal/successor/priorworkONLY viafixedguard8hops total/per332073,2searchcalls6queries wholelane prepaid/fullresponsesaved. Eachmanuallyselectedsingleplan,noURLbatch/traversal/HEAD/browser/HTTPcustomclient/TLS/cookiebypass. Failurewholeartifactunavailableallnewdeliveries, no retry. Sourcefinal/version/publicprior gatingseparate. Cached4currentregistryheadsnavigationonly, actualidentifiedmatchingproofbodyifconcretehit. No worldwidepriorityassertion.

Give strongest significancecases: fullactualorthonormalminimaxfailsstrictlyonconnectedunweightedgraph vs sourceownunequalcommunityparagraph alreadyforeshadowingroutineconstruction. For routineexclusion needcompleteapplicableactualprimary-result-to-exact-endpoint bridge, notsmallness/shortness/standardgraphHaaralone. For noveltyPASS needboundedactualsource/priorproofandchronology review, notopenlabel/nohit. SpecificapplicableunreadtheoremHOLD;genericworldwideunknownnotautomaticveto. Independentreadall57acceptedstatementscopes+39prior trustedscopes(no certificates)forfamilyduplication. Doesstructurallyresembles alreadyacceptedbasis/latticeparameterfamily actuallysharequantifiedendpoint? Documentratherthankeywordmatch.

DELIVER REVIEW.md andINDEPENDENT-PROOF.md orGAP.md, IDkeyedreview.json allseparategates, exactsource-to-proofmap, strongestobjections+contrarycase, source/read/visual/access/resource/searchinventories, everyfailedreceipt/fullresponseplan/hashchain, mandatoryfrozenafterandactualallfilemanifestexactterminalnoncircularselfexclusions. IfscientificgatespassprovideDORMANTfull-literalLeanobligations inclliteralgraph/basis/normsupport/admissibleclass/positivewitnessandfulluniversalnegation, noimplementationdispatchhere. Rootonlyacceptance/credit,57/60unchanged. Complete personallywithoutchildren. No mathematicalprogramorLeanexecution.
'''
task='Independent focused review332073 in '+str(W)+'\n'+common.replace('LANE',str(W)).replace('TARGET','332073')+'\nSPECIFIC SCOPE\n'+detail
(W/'TASK.txt').write_text(task)
wbind={str(A/n):v['sha256'] for n,v in files.items()};wbind[str(A/'SHA256-MANIFEST.json')]=sha(A/'SHA256-MANIFEST.json')
for n in m['terminal_noncircular_self_exclusions']:wbind[str(A/n)]=sha(A/n)
for q in W.rglob('*'):
 if q.is_file() and q.name!='search-budget.json':wbind[str(q)]=sha(q)
save(W/'frozen-inputs.json',wbind);save(W/'ROOT-PREP.json',dict(utc=now,lane=str(W),target=332073,frozen=len(wbind),model='gpt-6.1-sol',reasoning='high',service='default',credit=0,campaign=57,protected_peers=['expanded-corpus-r440','expanded-corpus-r441']))

# Two fresh discovery reservations; prepare BOTH before launch, using retained IDs to avoid the sibling.
base_source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();base_tail=base_source[base_source.index('# Metadata selector:'):];base_tail=base_tail[:base_tail.rfind('\nprint(')]
prior_new_ids=[];prior_new_sources=[];ready=[]
for num,other in [(440,441),(441,440)]:
 L=P/f'expanded-corpus-r{num}';assert not L.exists()
 tail=base_tail.replace('selection-routing-r434.json',f'selection-routing-r{num}.json').replace('for num in range(421,434):','for num in range(421,440):')
 tail=tail.replace("active=['cmdrr-five-three-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r2']",'active='+repr([f'expanded-corpus-r{other}',W.name]))
 tail=tail.replace('peer_ids={326555,324571};peer_sources={\'https://arxiv.org/abs/1310.5240\',\'https://arxiv.org/abs/1211.6486\'}','peer_ids='+repr(set([326555,324571,332073]+prior_new_ids))+';peer_sources='+repr(set(['https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486','https://arxiv.org/abs/1512.05406']+prior_new_sources)))
 tail=tail.replace("'accepted_new':55","'accepted_new':57").replace('55/60','57/60')
 latest='''
LATEST ROOT:57/60beyond39accepted96total, ONLYGPT-6.1Solhigh/defaultALLagents/nochildren. NEW#56shoe324571uniformsup<=255/256<1allcountablelaws, literalstrictalternationfull28moduleLean/strict/checker+separatereplay+body/originauditpassedindependentreview;rootfixedreporting,prior404andprocesslimitsretained,noglobalnoveltyclaim. NEW#57CMDRR326555universalnonexistence39moduleLean/strict/checker/fullbodyandmetadataaudit+literal/finalsourcepassedindependentreview;rootacceptedCONTENTwithhistoricalr3metadatatraversal/missingreapevidenceUNRESOLVED/notwaived. Allrows/columns/normalization/sign/helpersonefamily,noadditionalcredit. Completeacceptedrecordsaredatedrootadjudications,staleauthor55/60credit0handbacksarehistorical. No activeformalwork intheseacceptedfamilies.
Currentplannedpeerwavelet332073independentreviewandSIBLINGdiscoveryentirelyprotectedfromread/hash/glob/list/poll evenmetadata. RootseparatesIDs/sourceURLsusingretainedmetadata. r439all0:327053latticefirsttwo2designshells/thirdnotordinaryproposalPARKEDactualJNT10.1016/j.jnt.2014.02.015/1401.2891final403ALLnewalternatebodydeliverydenied;cachedoriginal/thesisonlywherecopied.332073graphwaveletK1K3bridgeK5ordinaryminimaxproposalawaitsindependentsource/basisconstraints/prior-significancereview,notreadyformal. ExactcurrentMathDB327053/332073recordchallenge-suffixunavailableacrossdelivery,transport200historypreserved/noguardbackfill;no scripts.330708mobiusfiber-surjectivity/cancellationunpaid.17otherprimarybodiesunread. r438332892Z6MAXgammafoursetordinaryproposalPARKEDactualMathematika10.1112/S0025579315000157/1307.8396final403ALLnewdeliveriesdenied;noformal/noveltycredit. r437341052N8Gaussianroundingordinary/probabilityPASSbutexactYe1999DOI10.1007/s10107980012aunavailableafterblockedHTTPredirect,sourcefinal/significancePARKED;noexpectationclaimrefuted. Artifactwidealloldr39576acquisitionsquarantineretained.
Readactualsourcehypotheses,strongerexistingtheoremsandproofsBEFOREmajorinvestment; same-sourceconjecturescanalreadyfollowfromanother theorem orprovidedexample. Source-own/publicproofs/routinecompletebridges/wording-domainendpointcorrectionsZERO. Do not excludeonshortness/standardtool/smallwitnessalone. SpecificapplicableunreadtheoremHOLD,genericworldwideunknownnotautomaticveto,boundednonmatchnotglobalnovelty. Historicaldigit/hashsubstringandneighborIDdispositiontransfersprohibited;matchactualIDkeys/sourcefieldsbeforeclaim. Allrootintakesdocumentaryorchestrationonly,notnewmath/computation.
'''.replace('SIBLING',f'expanded-corpus-r{other}')
 tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(latest),tail,count=1,flags=re.S)
 ns=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+f'#complete-metadata-r{num}','exec'),ns)
 rr=json.loads((L/'reservation.json').read_text());assert not set(rr['ids'])&set(prior_new_ids)
 prior_new_ids+=rr['ids'];prior_new_sources +=[x.get('source_url') for x in rr['rows']]
 assert len(json.loads((L/'frozen-inputs.json').read_text()))==12
 ready.append(dict(lane=str(L),task_sha256=sha(L/'TASK.txt'),ids=rr['ids'],role='research'))
ready.append(dict(lane=str(W),task_sha256=sha(W/'TASK.txt'),ids=[332073],role='review'))
for row in ready:
 lane=Path(row['lane']);assert not (lane/'bootstrap-receipt.json').exists();fb=json.loads((lane/'frozen-inputs.json').read_text());assert all(sha(Path(n))==v for n,v in fb.items())
save(ROOT/'r440-r441-wavelet-ready.json',dict(utc=now,accepted_new=57,target_new=60,previous_accepted=39,packets=ready,latest_denials=str(denpath),model='gpt-6.1-sol',reasoning='high',service='default',credit=0))
print(json.dumps(dict(accepted_new=57,review_lane=str(W),discovery_lanes=[r['lane'] for r in ready[:2]],discovery_IDs=prior_new_ids,review_frozen=len(wbind),r439_files_verified=len(files))))
