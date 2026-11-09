import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
A=P/'binary-projection-ratio-source-review-sol-r1';L=P/'expanded-corpus-r438'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==55 and not L.exists()
m=json.loads((A/'SHA-MANIFEST.json').read_text());rows=m['files'];assert len(rows)==100
assert all(sha(A/v['path'])==v['sha256'] for v in rows)
assert (A/'SHA-MANIFEST.sha256').read_text().split()[0]==sha(A/'SHA-MANIFEST.json')
f=json.loads((A/'frozen-inputs.json').read_text());assert len(f)==177
for n,v in f.items():
 assert 'cmdrr-five-three-formal-independent-review-sol-r5' not in n and 'shoe-pair-discrepancy-formal-independent-review-sol-r6' not in n
 assert sha(Path(n))==v
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==177 and after['mismatches']==[]
rec=[]
for row in rows:
 if row['path'].endswith('.receipt.json'):
  j=json.loads((A/row['path']).read_text());rec.append(dict(path=row['path'],sha256=row['sha256'],exit=j.get('exit'),killed=j.get('killed')))
n='seal_manifest.receipt.json';j=json.loads((A/n).read_text());assert j['exit']==0;rec.append(dict(path=n,sha256=sha(A/n),exit=j['exit'],terminal=True))
prev='0'*64;events=[]
for i,b in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 j=json.loads(b);assert j['seq']==i and j['previous']==prev;prev=dg(b);events.append(j)
 if j['event']=='success':assert sha(A/j['destination'])==j['sha256']
assert sum(j['event']=='attempt' for j in events)==3 and sum(j['event']=='success' for j in events)==1
assert events[-1]['event']=='redirect' and events[-1]['location']=='http://link.springer.com/10.1007/s10107980012a'
access=json.loads((A/'access-inventory.json').read_text());assert access['actual_get_hops']==3
assert 'PolicyError' in (A/'get_ye_primary.output.txt').read_text() and 'HTTPS' in (A/'get_ye_primary.output.txt').read_text()
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==2 and budget['queries_used']==6
gates=json.loads((A/'keyedreview.json').read_text())
parent=P/'binary-projection-ratio-source-parent-integration-sol-r1.json'
record=dict(utc=now,mathdb_id=341052,reviewed_lane=str(A),manifest_files_verified=len(rows),manifest_sha256=sha(A/'SHA-MANIFEST.json'),manifest_mismatches=[],frozen_verified=len(f),frozen_mismatches=[],frozen_after=after,receipts=rec,receipt_count=len(rec),receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in rec)),actual_GET_hops=3,GET_successes=1,redirect_response=1,guard_chain_verified=True,guard_chain_tail_sha256=prev,search_calls=2,querystrings=6,review_gates=gates,
 root_disposition='PARK scientific qualification; no new formalization or same-work retrieval lane. Independent ordinary/probability/source-v1 PASS retained, no new credit. Exact cited Ye1999 work is unavailable after policy-rejected HTTP redirect; final-publication identity and exact Nesterov1998/2000 comparisons/significance remain unpaid. Additional partial comparisons cannot erase the specific unread Ye proof obligation.',
 ordinary_scope='Author and independent reviewer prove a genuine global SDP optimum and strictly feasible binary sign output on an open positive-probability event, including every eigenbasis and fixed finite search. No refutation of expectation/existence/high-probability or specially chosen optimum claimed.',
 significance_scope='Potential deterministic-vs-expected rounding quantifier correction remains concrete concern, not adjudicated as routine without a complete applicable prior/correction bridge. No novelty/significance PASS from shortness/open status/root heads or generic worldwide unknown.',
 network_process='Reviewer FAIL/QUARANTINE retained. Actual HTTPS DOI request returned HTTP302; redirected non-HTTPS request was blocked before dispatch. Failure logger also rejected the HTTP URL, so no unavailable row was written. Original ledger unchanged; root records artifact-wide denial separately. Wrapper runner exit0 does not imply guard acquisition success: two guard exits1 and tracebacks preserved. No forbidden HTTP request, TLS bypass or retry claimed.',
 root_scope='Documentary integrity/orchestration and review adjudication only; no mathematical/compiler execution',credit=0,accepted_new=55,target_new=60,previous_accepted=39)
save(parent,record)
den=json.loads((ROOT/'inherited-denials-r437.json').read_text());den['utc']=now
blocked=[('https://www.ecs.umass.edu/mduarte/Publications.html','Marco Duarte current publication-page artifact', 'TLS certificate verification failed before body; all alternate delivery of this publication-page artifact unavailable, no TLS bypass. Not a blanket denial of every distinct Duarte paper.'),('https://doi.org/10.1007/s10107980012a','Ye1999 Approximating quadratic programming with bound and quadratic constraints, Mathematical Programming84(2)219-226, DOI10.1007/s10107980012a','HTTPS DOI302 to HTTP Springer URL; target request rejected before dispatch, failure-logger PolicyError preserved. ENTIRE identified Ye1999 work unavailable across HTTPS-upgrades/alternatehosts/queries/versions/cache/mirrors/author/manuscript/DOI deliveries. No retry or indirect recovery.')]
for url,artifact,reason in blocked:
 key=url.removeprefix('https://').lower()
 if key not in den['blocked_keys']:den['blocked_keys'].append(key)
 if artifact not in den['blocked_artifacts']:den['blocked_artifacts'].append(artifact)
 den['records'].append(dict(url=url,reason=dict(artifact=artifact,restriction=reason,body_obtained=False),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'),failure_output=str(A/('get_ye_primary.output.txt' if 'doi.org' in url else 'get_publication_identity.output.txt')),failure_output_sha256=sha(A/('get_ye_primary.output.txt' if 'doi.org' in url else 'get_publication_identity.output.txt'))),root_record='New immutable union entry only; no historical guard-ledger repair/backfill'))
den['blocked_keys']=sorted(set(den['blocked_keys']))
den['root_binary341052_scope']='Ordinary/probability/v1 PASS but scientific qualification PARKED. Exact Ye1999work10107980012a unavailable artifact-wide after blockedHTTPredirect; preserve missing unavailable ledger row and guard failures, no HTTPS-upgrade or alternate retrieval. Current Duarte Publications page TLS-unavailable artifact only, not blanket all papers. ExactNesterov1998OMS/2000chapter UNREAD, not denied by Ye failure, but they do not alone discharge Ye/source/significance holds. No formal dispatch or credited quantifier correction.'
denpath=ROOT/'inherited-denials-r438.json';save(denpath,den)

# Reuse the complete metadata-only preparer with active review paths excluded before stat/open.
source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();tail=source[source.index('# Metadata selector:'):];tail=tail[:tail.rfind('\nprint(')]
tail=tail.replace('selection-routing-r434.json','selection-routing-r438.json').replace('for num in range(421,434):','for num in range(421,438):')
tail=tail.replace('cmdrr-five-three-formal-sol-r3','cmdrr-five-three-formal-independent-review-sol-r5').replace('shoe-pair-discrepancy-formal-sol-r2','shoe-pair-discrepancy-formal-independent-review-sol-r6')
tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2','cactus-randic-ratio-source-review-sol-r1','binary-projection-ratio-source-review-sol-r1']:")
latest='''
LATEST ROOT ROUTING:55/60beyond39accepted94total. ONLYGPT-6.1Solhigh/defaultALLagents,nochildren. Activecmdrr-five-three-formal-independent-review-sol-r5 andshoe-pair-discrepancy-formal-independent-review-sol-r6 entirelyprotectedfromread/hash/glob/list/poll evenmetadata; root excludes326555/324571 and1310.5240/1211.6486 fromthis20usingretainedmetadata. CMDRR authorfulluniversalnonexistence39source/proof/control/auditmodulesstrict+freshchecker receiptsverified, independentfinalreview/processadjudicationUNPAID, r3metadatatraversal/missingreapreceiptbreachretained. ShoeauthorfullPMFNat/countablelawuniformsup<=255/256<1,28modulefreshstrict/checker,259productionroots29367reachablebodygraph; independentfinalreviewstillUNPAID. PriorincompleteShoeindependentreviewstoppedbeforecompileraftertwoownlogguessesrejectedbeforecontentdisplay,1596frozenintact. Rootretainsdeviationandnewr6receipt-drivenlogdisplay,notmathematicalrejectionorblanketwaiver. Neitherfamilyaccepted/recountable.
Completedr437all0:341052independentordinary/probability/v1refutationPASS,N8SDPactualoptimumandpositiveGaussianbadcone7/16<pi/2-1evenfiniteLselection; SCIENTIFICPARKED exactYe1999Prop1unreadandwholeworkDOI10.1007/s10107980012a nowunavailableafterpolicyblockedHTTPredirect+failureloggererror(noHTTPtargetrequestsent),currentDuartepublicationpageTLSunavailable,exact1998OMS/2000Nesterovchapterunreadnotdenied. Noformaldispatch/newretrievalofblockedwork. Expectation-vs-pointwise/algorithmquantifiercorrectionconcernconcrete,notautomaticroutineexclusionwithoutcompletepriorbridge,nosignificancecredit.340572sourcePhi_nshellingnotweakorderintervalcontractibility,fullfiberreachabilitygap;340526n3strictnesssourcecorrectionandpublicCraignonnegativeidentityproofzero,notnewliteralparityequivalence. Other17primarybodiesunread. r436342217/343211/343592fullscopeproofsunpaid,343211JLMS10.1112/jlms.12484finalUNREADnotdenied; actualIDkeys/sourcefieldsforhistory,neverhashdigits/neighbordispositiontransfer.
351165cactusnumericalsubsetcompleteactualsourcehalfdiametercorollaryzero;undefinedsymmetry/mixedequality/full-literalGAP,noformal/retrievallane. r434349307actualpublicDingYanjointcycleJfractionproofzero;356364source-owncycleexceptioncorrectionzero;354623sourcecochordalcounterexampleszero.323710coverratioordinaryPASSbutactualJGT2017final10.1002/jgt.22029body403ALLalternate deliveryunavailable=>PARK;323059regularMISv1PASSbutOrder2013final10.1007/s11083-012-9253-5cookie-loopunavailable=>PARK. Source-own/publicsolutions/routinefullybridgedresults/wording-domainendpointcorrectionszero. Read actual primary definitions,strongerexistingtheoremsandproofsBEFORElargeproofinvestment; a printedconjecturecanalreadyfollowfromanothertheoreminsamepaper. Everyinheriteddenialandallr39576acquisitionquarantinebinding. NO TLS/cookie/redirectupgrade/alternatehost/version/cache/bodydeliveryretryafterfailure. Genericworldwideunknownnotautomaticveto;specificapplicableunreadtheorempreciseHOLD;boundednonmatchnotworldwidenovelty. Allcompletedrootintakesdocumentaryorchestrationonly,no mathematicalprogram/compiler execution.
'''
tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(latest),tail,count=1,flags=re.S)
namespace=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+'#complete-metadata-r438','exec'),namespace)
t=(L/'TASK.txt').read_text()
for word in ['Resources fixed:','Deliver actual','receiptJSON','wholelane maximum3 actual calls9','cmdrr-five-three-formal-independent-review-sol-r5','shoe-pair-discrepancy-formal-independent-review-sol-r6']:assert word in t,word
b=json.loads((L/'frozen-inputs.json').read_text());assert len(b)==12 and all(sha(Path(n))==v for n,v in b.items());assert not (L/'bootstrap-receipt.json').exists()
ready=dict(utc=now,lane=str(L),ids=json.loads((L/'reservation.json').read_text())['ids'],task_sha256=sha(L/'TASK.txt'),parent_integration=str(parent),latest_denials=str(denpath),accepted_new=55,credit=0,active_peers=['cmdrr-five-three-formal-independent-review-sol-r5','shoe-pair-discrepancy-formal-independent-review-sol-r6'],model='gpt-6.1-sol',reasoning='high',service='default',root_role='Documentary integrity/orchestration only')
save(ROOT/'r438-ready.json',ready);print(json.dumps(ready))
