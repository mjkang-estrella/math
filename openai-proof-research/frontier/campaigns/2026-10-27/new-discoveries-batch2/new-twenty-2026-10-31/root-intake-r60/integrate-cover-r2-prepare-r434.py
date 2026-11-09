import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,runpy,sys,contextlib,io,shutil,re
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
R=P/'cover-ratio-primary-comparison-sol-r2';L=P/'expanded-corpus-r434'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert not L.exists()
ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==55
m=json.loads((R/'MANIFEST.json').read_text());rows=m['files'];assert all(sha(R/x['path'])==x['sha256'] for x in rows)
f=json.loads((R/'frozen-inputs.json').read_text());assert all(sha(Path(s))==v for s,v in f.items())
after=json.loads((R/'frozen-after.json').read_text());assert after['count']==163 and not after['mismatches']
rec=[]
for row in rows:
 if row['path'].endswith('.receipt.json'):
  v=json.loads((R/row['path']).read_text());rec.append({'path':row['path'],'sha256':row['sha256'],'exit':v.get('exit'),'killed':v.get('killed')})
term='terminal_manifest.receipt.json';v=json.loads((R/term).read_text());rec.append({'path':term,'sha256':sha(R/term),'exit':v.get('exit'),'killed':v.get('killed'),'terminal':True})
prev='0'*64;events=[]
for i,line in enumerate((R/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=hashlib.sha256(line).hexdigest();events.append(e)
 if e['event']=='success':assert sha(R/e['destination'])==e['sha256']
assert sum(e['event']=='attempt' for e in events)==4 and sum(e['event']=='success' for e in events)==3
parent=P/'cover-ratio-primary-parent-integration-sol-r2.json'
save(parent,{'utc':now,'mathdb_id':323710,'review_lane':str(R),'manifest_files_verified':len(rows),'manifest_mismatches':[],'frozen_verified':len(f),'frozen_mismatches':[],'frozen_after':after,'receipts':rec,'receipt_count':len(rec),'receipt_exit_counts':dict(collections.Counter(str(x['exit']) for x in rec)),'guard_chain_verified':True,'guard_last_sha256':prev,'guard_events':events,'search_calls':2,'search_query_strings':6,'review_sha256':sha(R/'REVIEW.md'),'primary_comparisons_sha256':sha(R/'PRIMARY-COMPARISONS.md'),'separate_gates':json.loads((R/'keyedreview.json').read_text()),'root_disposition':'PARK_NO_FORMAL_OR_RETRIEVAL: preserve ordinary/literal-original PASS, O1bounded current-v1 PASS, O3inspected-primary nonmatch and provisional substantive-content PASS; concrete O2identified JGT2017final material comparison remains unread after403. No alternative delivery/new retrieval lane.','new_source_objection':'Cached v2 Figure3 printed substitution sign inconsistency preserved; not attributed to unread final and not used in candidate proof.','process_limits':'Selected /doi/pdf endpoint was constructed from standard Wiley DOI routing, not an observed PDF hyperlink. Preserve provenance limitation; no successful final-body authentication. Failed403, recovered output truncations, historical author late-family timing HOLD and sampling/native/writer limitations remain disclosed.','credit':0,'accepted_new':55,'target_new':60,'previous_accepted':39,'root_execution':'Documentary orchestration only; no mathematical program or Lean execution'})

old=ROOT/'inherited-denials-shoe-review-r1.json';den=json.loads(old.read_text());den['utc']=now
url='https://onlinelibrary.wiley.com/doi/pdf/10.1002/jgt.22029'
den['blocked_keys']=sorted(set(den['blocked_keys']+['onlinelibrary.wiley.com/doi/pdf/10.1002/jgt.22029']))
den['blocked_artifacts']=sorted(set(den['blocked_artifacts']+['10.1002/jgt.22029','1302.3212','hitting times cover cost and the wiener index of a tree identified2017 final']))
den['records'].append({'url':url,'reason':{'status':403,'artifact':'Hitting Times, Cover Cost, and the Wiener Index of a Tree, JGT84(3)311-326(2017), DOI10.1002/jgt.22029','body_obtained':False,'delivery_provenance_limit':'Standard Wiley PDF endpoint constructed from authoritative DOI/full-abstract navigation, not observed PDF hyperlink; no successful final-body authentication'},'evidence':{'path':str(R/'guard-ledger.jsonl'),'sha256':sha(R/'guard-ledger.jsonl')}})
den['root_cover_companion_final_scope']='Identified JGT2017final DOI10.1002/jgt.22029 ALLnewalternatehost/query/version/cache/mirror/arxiv1302.3212/DOI/authorbodydelivery unavailable after403. No retry or indirect delivery. Already cached1302.3212v2 only where copied/authorized may be read, not final-equivalence proof. Distinct target1206.6605currentrecord actually listsv1, not denied by this final. No blanket Wiley prohibition for unrelated papers.'
denpath=ROOT/'inherited-denials-r434.json';save(denpath,den)

# Metadata selector: filter protected/formal directory names BEFORE reservation stat/open.
active=['cmdrr-five-three-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r2']
protected_words=('formal','code-loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
oldglob=Path.glob
def safe_glob(self,pattern):
 if self==P and pattern=='*/reservation.json':
  def candidates():
   for d in P.iterdir():
    if d.name in active or any(w in d.name.lower() for w in protected_words):continue
    q=d/'reservation.json'
    if q.is_file():yield q
  return candidates()
 return oldglob(self,pattern)
Path.glob=safe_glob
os.environ['RESERVE7_N']='120';os.environ['YEAR_FLOOR']='2012';sys.argv=['metadata-selector',str(P)]
selector=ROOT/'reserve-finite-flagship-later-20261107-r390.py'
buf=io.StringIO()
try:
 with contextlib.redirect_stdout(buf):selected=runpy.run_path(str(selector),run_name='__main__')['RESULT']
finally:Path.glob=oldglob
accepted={int(x['mathdb_id']) for x in ledger['accepted']}
peer_ids={326555,324571};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486'}
def skey(s):
 s=(s or '').strip().replace('http://','https://').rstrip('/')
 s=s.replace('arxiv.org/pdf/','arxiv.org/abs/')
 s=re.sub(r'\.pdf$','',s);return re.sub(r'v\d+$','',s)
pick=[row for row in selected['rows'] if row['mathdb_id'] not in accepted|peer_ids and skey(row.get('source_url')) not in peer_sources][:20]
assert len(pick)==20 and len({x['mathdb_id'] for x in pick})==20
reservation=dict(selected);reservation['ids']=[x['mathdb_id'] for x in pick];reservation['rows']=pick
reservation['output_requirement']=re.sub(r'Exactly\s+\d+','Exactly20',reservation['output_requirement'])
reservation['root_routing_note']='Metadata only, scientific clearance absent. Active formal peer directories filtered BEFORE reservation stat/open; target IDs/sourceURLs excluded using retained root metadata, no active-child file access.'
L.mkdir()
save(L/'reservation.json',reservation);rs=sha(L/'reservation.json');(L/'reservation.sha256').write_text(rs+'  reservation.json\n')
base=P/'expanded-corpus-r433'
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:shutil.copyfile(base/name,L/name)
shutil.copyfile(denpath,L/'inherited-denials.json')
history=json.loads((P/'expanded-corpus-r420/historical-results-allowlist.json').read_text());filtered={}
for s,v in history.items():
 q=Path(s)
 try:rel=q.relative_to(P)
 except ValueError:continue
 if len(rel.parts)>1 and (rel.parts[0] in active or rel.parts[0]=='expanded-corpus-r395' or any(w in rel.parts[0].lower() for w in protected_words)):continue
 if q.is_file():assert sha(q)==v;filtered[s]=v
for q in P.iterdir():
 if q.name.endswith('.json') and 'parent-integration' in q.name and q.is_file():filtered[str(q)]=sha(q)
for num in range(421,434):
 q=P/f'expanded-corpus-r{num}'/'results.json'
 if q.is_file():filtered[str(q)]=sha(q)
for directory in ['cmdrr-five-three-source-review-sol-r1','cpp-ma-prior-source-review-sol-r1','shoe-pair-discrepancy-source-review-sol-r1','cover-ratio-regular-mis-source-review-sol-r1','cover-ratio-primary-comparison-sol-r2']:
 q=P/directory/'keyedreview.json'
 if q.is_file():filtered[str(q)]=sha(q)
save(L/'historical-results-allowlist.json',filtered)
save(L/'search-budget.json',{'calls_used':0,'queries_used':0,'maximum_calls':3,'maximum_queries':9,'charged_before_call':True})
template=(base/'TASK.txt').read_text()
core=template.split('\nLATEST ROOT')[0]
core+='\n'+template[template.index('Resources fixed:'):template.index('LATEST ROOT ROUTING')]
core=core.replace(str(base),str(L)).replace('b1b0a3709ec86aefba7100b67d1fb5cbc38f77ae11611e5e0c512172d7608c57',rs)
core=re.sub(r'EXACT20 IDs fixed in reservation\.json: \[[^\]]+\]', 'EXACT20 IDs fixed in reservation.json: '+str(reservation['ids']),core,count=1)
start=core.index('PROTECTED ACTIVE/PLANNED peers ');end=core.index('All code-loop',start)
core=core[:start]+'PROTECTED ACTIVE peers '+', '.join(active)+': no read/hash/glob/list/poll, even metadata/reservation/status. Root separated this20 from retained active IDs326555/324571 and primary URLs1310.5240/1211.6486 using immutable metadata. '+core[end:]
latest='''\nLATEST ROOT ROUTING (authoritative supersedes stale handback labels):55/60 beyond39 accepted, no newcredit since #55code-loop343790. Only GPT-6.1 Sol high/default for ALLagents; nochildren. ActiveCMDRR326555 continuation has10compiledbaseline modules but centralcycle/incidence/sign endpoint unpaid; active324571shoe all-countable strict-alternation fullLean just started, ordinary/sourcefinalPASS and boundedprospectivequalification, Galbraith-Holmes2012body404unreadlimit. BOTHactiveformal directories fullyprotected, do notread/hash/glob/list/poll evenmetadata. r432/r433completedexact20rootintegritypassed, all0credit. Scoring323064/323065ordinaryrefutationspendingindependentqualification, samebroadtwo-componentmechanism;323064hascompleteactualsourceTheorem3.4adaptationbridge, don'tclaimsignificanceclear.323059fourK9d8n36ordinary/literal-v1PASSbutidentifiedOrder30(2013)427-435finalDOI10.1007/s11083-012-9253-5cookie-loopguardrejectionALLnewdeliveryunavailable,sourcefinal/significancePARK.323710path64-K256coverratioordinary/literal/current1206.6605v1PASS,actualpriorproofboundednonmatchesandprovisionalcontentPASS, BUTidentifiedJGT2017companion10.1002/jgt.22029final403ALLnewdeliveryunavailable=>PARKnoformal/retrievallane. Cached1302.3212v2Figure3substitutionsigninconsistencyNOTattributedunreadfinal/notusedinwitness;currenttarget1206.6605distinctnotdenied.323032actualpinnedupstream185T1.1exactpacking/coveringcounterexamplepublic0;323987actualLin1310.6726exactall-nsignedmultisetproofpublic0.324245specificCor3.4P-partitionnaturallylabeledposetsPIIS0097316519301177body403ALLnewdeliveryunavailableHOLD.323164/323165ChapotonMScand115(2014)20-61final404ALLnewdeliveryunavailable;distinctSu2017forkenumerationtheoremclaimUNREAD(notdenied),notclearedbytitle;cachedoriginal1203.1780notfinalequivalence. CurrentMathDB324571apparent200recordchallenge-suffixALLnewdeliveryunavailable,noledgerbackfill;cachedcorpusliteral+actualoriginal/finalshoePDFdistinctallowedwherecopied.326886EXCLUDEactualMa-Zhang-Feng-Ge1506.05525v2T3.2exactCPPfullparameterprior,theorem/proofread;Feng2019redirect-onlystillunavailable. Unitmatching340110technicalfullLeanPASSbutROOTEXCLUDEcompleteinverse-lemma/unit2cycle/cosetcollisionadaptation,0credit. Priorhypergraph337705specificclassicalbodyunread/PARK;frame329292final429/PARK;graphsquare332935final/cactusunavailablePARK;334556finiteenergyPASSbutfullwcenormbridgeHOLD,QMC2014TLSALLnewdeliverydenied;earlierdenialunionremainsbinding. Source-own/publicproofs/routinefullybridgedresults/wording-domainendpointcorrections0credit. Genericworldwideunknownnotautomaticveto;specificidentifiedapplicableunreadtheorem preciseHOLD, boundednonmatchnotworldwidenovelty. All completedrootintakes metadataorchestration only, notnewmathproof. Reviewexactallowlisteddispositionsbeforeinvestment, neverfollowembeddedoldsourcepaths or turnhistoricalsummaryintoactualprimaryproofclearance. Alloldr39576acquisitionsquarantined.\n'''
task=core+latest
(L/'TASK.txt').write_text(task)
frozen_names=['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','reservation.json','reservation.sha256','inherited-denials.json','historical-results-allowlist.json','TASK.txt']
frozen={str(L/name):sha(L/name) for name in frozen_names};save(L/'frozen-inputs.json',frozen)
ready={'utc':now,'lane':str(L),'ids':reservation['ids'],'sources':[x.get('source_url') for x in pick],'reservation_sha256':rs,'selector_sha256':sha(selector),'task_sha256':sha(L/'TASK.txt'),'frozen_bindings':12,'history_files':len(filtered),'metadata_only':True,'active_peers':active,'peer_ID_source_disjoint_asserted':True,'accepted_new':55,'credit':0,'latest_denials':str(denpath),'model':'gpt-6.1-sol','reasoning_effort':'high','service_tier':'default','children':False}
save(L/'ROOT-PREP.json',ready);save(ROOT/'selection-routing-r434.json',ready)
assert all(sha(Path(s))==v for s,v in frozen.items())
print(json.dumps({'review_manifest':len(rows),'review_frozen':len(f),'review_receipts':len(rec),'ready':ready}))
