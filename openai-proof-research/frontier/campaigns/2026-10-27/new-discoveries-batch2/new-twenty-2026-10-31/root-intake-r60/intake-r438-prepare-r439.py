import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil,base64,ast
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r438';L=P/'expanded-corpus-r439'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==55 and not L.exists()
m=json.loads((A/'SHA256SUMS.json').read_text());files=m['files'];assert len(files)==138 and all(sha(A/n)==v['sha256'] for n,v in files.items())
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==12 and all(sha(Path(n))==v for n,v in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==12 and after['mismatches']==[]
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];assert len(ids)==20 and sha(A/'reservation.json')==(A/'reservation.sha256').read_text().split()[0]
prov=json.loads((A/'literal-provenance.json').read_text());gates=json.loads((A/'results.json').read_text());assert set(map(int,prov))==set(ids)==set(map(int,gates));chunks={};bindings=[]
for key,row in prov.items():
 q=Path(row['chunk'])
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert raw==base64.b64decode(row['raw_line_base64']) and dg(raw)==row['raw_sha256'] and raw.endswith(b'\n') and row['newline']
 obj=json.loads(raw);assert obj==row['object'] and obj['mathdb_id']==int(key)
 tok=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert tok==row['statement_token'].encode() and dg(tok)==row['statement_token_sha256']
 assert obj['statement']==row['statement_utf8'] and dg(row['statement_utf8'].encode())==row['statement_utf8_sha256']
 bindings.append(dict(id=int(key),chunk=str(q),line=row['line'],raw_sha256=row['raw_sha256'],token_sha256=row['statement_token_sha256'],statement_sha256=row['statement_utf8_sha256']))
prev='0'*64;events=[]
for i,b in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 j=json.loads(b);assert j['seq']==i and j['previous']==prev;prev=dg(b);events.append(j)
 if j['event']=='success':assert sha(A/j['destination'])==j['sha256']
attempts=[j for j in events if j['event']=='attempt'];successes=[j for j in events if j['event']=='success'];failed=[j for j in events if j['event']=='unavailable']
assert len(attempts)==14 and len(successes)==12 and len(failed)==1 and failed[0]['status']==403 and failed[0]['artifacts']==['10.1112/s0025579315000157']
charges=collections.Counter(str(k) for j in attempts for k in j['routes']);assert max(charges.values())<=12
receipts=[]
for n in [n for n in files if n.endswith('.receipt.json')]+[n for n in m['terminal_noncircular_self_exclusions'] if n.endswith('.receipt.json')]:
 j=json.loads((A/n).read_text());receipts.append(dict(path=n,sha256=sha(A/n),exit=j.get('exit'),killed=j.get('killed')))
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
parent=P/'expanded-corpus-r438-parent-integration.json'
record=dict(utc=now,lane=str(A),manifest_files_verified=len(files),manifest_sha256=sha(A/'SHA256SUMS.json'),manifest_mismatches=[],frozen_verified=12,frozen_mismatches=[],frozen_after=after,literal_bindings=bindings,all20_gate_records=gates,receipts=receipts,receipt_count=len(receipts),receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_chain_verified=True,guard_tail_sha256=prev,GET_hops=14,GET_successes=12,redirects=1,unavailable=failed,GET_charges=dict(charges),search_calls=3,queries=9,
 root_disposition='No qualified survivor or credit.332892 investigator full ordinary n-tuple MAX-gamma refutation retained, scientific PARKED at identified Mathematika final403 and independent prior/significance/fidelity review unpaid. No formal dispatch or new delivery of denied work.337263/337264 one equivalent source family, rank3orientedconfluence unpaid;336833actualsourceExample12 and337479Kimpublicproof zero-credit within recorded body/visual limits.',
 reading_scope='All20literals;6primary bodies with selected reading/actual proof limits. Remaining14 target primary bodies unread. Only promotionFigure4 visually read. Kim diagrams not visually inspected, so no fullvisual proofPASS; heads/snippets/rootnohit not novelty clearance.',
 scientific_limits='Source original gamma=MAX and all four summands size2 are paid by investigator; final article could contain correction/discussion. No routine exclusion or novelty PASS from simple subgroup saturation alone. No independent ordinary proof accepted as root mathematics.',
 root_scope='Documentary integrity/orchestration only; no mathematical programs/compiler execution',credit=0,accepted_new=55,target_new=60,previous_accepted=39)
save(parent,record)
den=json.loads((ROOT/'inherited-denials-r438.json').read_text());den['utc']=now
e=failed[0];den['blocked_keys']=sorted(set(den['blocked_keys']+[e['url_key'],'doi.org/10.1112/S0025579315000157']))
den['blocked_artifacts']=sorted(set(den['blocked_artifacts']+e['artifacts']+['1307.8396']))
den['records'].append(dict(url=e['url'],reason=dict(status=403,artifact='Tringali Mathematika62 Cauchy-Davenport theorem for semigroups, DOI10.1112/S0025579315000157; original1307.8396',body_obtained=False,restriction='Entire identified final/article work unavailable across all alternatehost/query/version/cache/mirror/author/DOI/arxiv body deliveries; no retry. Cached originals/laternote only where explicitlycopied/authorized; no finalequivalence assumed.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'))))
den['root_r438_sumset332892_scope']='Full ordinary investigator n4,Z6 tuple {0,1},{0,3},{0,3},{0,3}:sumcard4,maxgamma6,cardbound5, evenolderallsize>=2. ScientificPARKED finalMathematika10.1112/S0025579315000157body403 nowALLalternate delivery unavailable,original1307.8396 sameworkblocked. Alreadycached1604.02136v2laternote+1307.8396v2 maybereadonlywhenexplicitcopied, not finalequivalence. No independent/prior/significance/Lean acceptance. Equivalentfactorization337263/337264onefamilyincomplete.12successfulpayloads/14hops,3search9queries,all0credit.'
denpath=ROOT/'inherited-denials-r439.json';save(denpath,den)

# Complete metadata preparer, filtering active/formal names BEFORE reservation stat/open.
source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();tail=source[source.index('# Metadata selector:'):];tail=tail[:tail.rfind('\nprint(')]
tail=tail.replace('selection-routing-r434.json','selection-routing-r439.json').replace('for num in range(421,434):','for num in range(421,439):')
tail=tail.replace('cmdrr-five-three-formal-sol-r3','cmdrr-five-three-formal-independent-review-sol-r6').replace('shoe-pair-discrepancy-formal-sol-r2','shoe-pair-discrepancy-formal-independent-review-sol-r6')
tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2','cactus-randic-ratio-source-review-sol-r1','binary-projection-ratio-source-review-sol-r1']:")
tree=ast.parse((ROOT/'intake-binary-review-r1-prepare-r438.py').read_text())
oldlatest=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='latest' for t in n.targets))
latest='''
LATEST COMPLETED r438:all20literalbindings/sourceprooflimits/138manifestverified,zeroacceptedcredit.332892n4Z6MAXgammaordinaryrefutationproposalretainedbutSCIENTIFICPARKED,identifiedactualMathematikaDOI10.1112/S0025579315000157returned403afterDOIredirect:ALLnewalternatehost/query/version/cache/mirror/author/arxiv1307.8396bodydeliveryunavailable. No retry or finalequivalencefromcachedoriginal/later1604.02136v2note. Noindependentmathematical/prior/significanceclearanceorformaldispatch. Smallsubgroupsaturationnotautomaticroutineexclusionwithoutcompletepriorbridge.337263/337264equivalentonefactorizationfamily,rank3orientedconfluenceunpaid;336833ownsourceExample12and337479actualKimproofzero,Kimvisualdiagramsuninspectedlimit. Other14primarybodiesunread.14hops12payloadsuccess1redirect1denial;3search9queries;12frozenintact. Rootnoleans/mathematicalexecution.
CURRENTactivecmdrr-five-three-formal-independent-review-sol-r6 andshoe-pair-discrepancy-formal-independent-review-sol-r6 entirelyprotected. CMDRRpreviousindependent39freshstrict/checkers+ordinary/DAG/controls/6pageQApasswithinlimits; remaining29production/auxbodyread+declaration-kind/native-safety metadata+source/prior/processclosure active. Rootfixedsmallpaperreportingonly,separatearchival6pagecopyallpagesviewed,noproof/Leanchange,noacceptance. Historicalr3metadatatraversal/missingreapevidenceretained. Neitherfamilymayberecounted;55/60unchanged.
'''+oldlatest.replace('cmdrr-five-three-formal-independent-review-sol-r5','cmdrr-five-three-formal-independent-review-sol-r6')
tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(latest),tail,count=1,flags=re.S)
namespace=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+'#complete-metadata-r439','exec'),namespace)
t=(L/'TASK.txt').read_text()
for word in ['Resources fixed:','Deliver actual','receiptJSON','wholelane maximum3 actual calls9','cmdrr-five-three-formal-independent-review-sol-r6','shoe-pair-discrepancy-formal-independent-review-sol-r6']:assert word in t,word
f=json.loads((L/'frozen-inputs.json').read_text());assert len(f)==12 and all(sha(Path(n))==v for n,v in f.items());assert not (L/'bootstrap-receipt.json').exists()
ready=dict(utc=now,lane=str(L),ids=json.loads((L/'reservation.json').read_text())['ids'],task_sha256=sha(L/'TASK.txt'),parent_integration=str(parent),latest_denials=str(denpath),accepted_new=55,credit=0,active_peers=['cmdrr-five-three-formal-independent-review-sol-r6','shoe-pair-discrepancy-formal-independent-review-sol-r6'],model='gpt-6.1-sol',reasoning='high',service='default')
save(ROOT/'r439-ready.json',ready);print(json.dumps(ready))
