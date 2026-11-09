import json,pathlib,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r597'
def write(n,d):(P/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def sig(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
f=json.loads((P/'flat-bindings.json').read_text())
for p in [L/'sol-mathdb-primary-qualified-breadth-r578'/'failures.json',L/'sol-edge-irregulator-manuscript-packet-r1'/'packet/helper_guard.py',pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md'),L.parent/'AGENTS.md']:f.append(sig(p))
write('flat-bindings.json',list({x['path']:x for x in f}.values()))
rows=json.loads((P/'literal-records.json').read_text());a={int(s.split('\t')[0]):s.strip().split('\t',2)[1:] for s in (P/'assessments.tsv').read_text().splitlines()};assert len(a)==50
source={321700:('1106.2355','Definition5.1/Conjecture5.2; text lines705-754'),325693:('1306.0431','Section6.2 Definition4/Lemma9/Conjecture1; lines1370-1456'),324902:('1301.6983','Conjecture1, Theorem5, definition H_n, Lemma6 selected proof; lines210-265,431-625')}
out=[]
for r in rows:
 i=r['mathdb_id'];status,reason=a[i];rest=status in ['HOLD_RESTORE','HOLD_WORDING','HOLD_SOURCE_AMBIGUITY'];s=source.get(i)
 out.append({**{k:v for k,v in r.items() if k!='record'},'title':r['record']['title'],'source_url':r['record']['source_url'],'disposition':status,'assessment':reason,'scope_flags':{'literal_record_statement_read':True,'self_contained_statement':not rest,'restoration_required':rest,'selected_primary_passage_read':s is not None,'whole_primary_body_read':False,'source_internal_proved_result_passage_read':i in [325693,324902],'closest_successor_body_read':False,'local_complete_proof':False,'full_dependency_audit':False,'current_registry_cleared':False,'novelty_cleared':False,'full_scope_result_certified':False},'primary_evidence':None if not s else {'url':'https://arxiv.org/html/'+s[0]+'v1','version':'v1','derivative':s[0]+'.txt','read_scope':s[1]},'credit':0,'remaining':'Primary restoration/body and successor/prior checks as applicable; current registry HOLD. No hypothesis-specific proof task requested.'})
write('dispositions.json',out);write('proposals.json',[])
# Administrative IDs are leads only, never proof evidence.
ids={r['mathdb_id'] for r in rows}
def collect(x):
 z=set()
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ['mathdb_id','related_mathdb_id'] and isinstance(v,int):z.add(v)
   if k=='mathdb_ids' and isinstance(v,list):z.update(i for i in v if isinstance(i,int))
   z|=collect(v)
 elif isinstance(x,list):
  for v in x:z|=collect(v)
 return z
prior={n:sorted(ids & collect(json.loads((L/'root-mathdb-accepted-exclusions-r304'/n).read_text()))) for n in ['accepted-exclusions.json','historical-dispositions.json']}
write('prior-context-check.json',{'r304_assigned_id_matches':prior,'r363_decision':'364119 excluded; preserved','r597_adjudications':'Retire338290/339564/372627; park337963; exclude366370 routine source restriction; park365437/365439 as one family. No changes.','other_preserved':'344924/386396/387650 incomplete;372522 proof gap not identity refutation; all other non-self-contained judgments outside assignment untouched','counts':'9 additional /39 total /next40; no count change','baseline':'5883 RECORD reviews, not self-contained or full technical statements','claude_r504':'all fifty reserved/unreviewed; never reassigned','sol_r596':'active; never reassigned'})
write('source-coverage.json',{'literal_record_statements':50,'self_contained_at_screening':sum(r['scope_flags']['self_contained_statement'] for r in out),'restoration_or_wording_flags':sum(r['scope_flags']['restoration_required'] for r in out),'selected_primary_passages':3,'whole_primary_bodies':0,'closest_successor_bodies':0,'local_complete_proofs':0,'full_dependency_audits':0,'current_registry':'unavailable HOLD','primary_read_details':{str(i):s[1] for i,s in source.items()},'executed_mathematical_calculations':[],'planned_only':['325693: a multiplicative-independence lemma would be needed; no finite matrix search run','327160: a fixed-k transfer calculation is an instance, not a uniform route; not run'],'public_source_exclusion':324902,'proposals':0})
write('failures.json',{'access_requests':{'MathDB':0,'arxiv_HTML':3,'status':'three HTTP200; no other live requests'},'parked':['r578 coloring HTML404','r578 author certificate failure','r578 Christensen-Hovey timeout','r542 OEIS A274199/internal403','AIM/Kourovka/EGRES/AIProofWatch','DMGT TLS','ProjectEuclid challenge','ResearchGate403','current proof registry unavailable HOLD'],'route_policy':'No retry/bypass or alternate-route fishing. No Google/GitHub API/raw/codeload/diff, ScienceDirect, browser/preview, account/contact/message/upload/publication.','deviations':['Structural head of corpus chunk0001 displayed unassigned records1 and partial2 before all20 chunk verification. Not counted/reviewed/reassigned; no scientific judgment on them.','Initial combined fifty-statement output truncated; middle rows11..33 reprinted in a bounded dedicated run and read. No truncated material counted as complete.','Attempt to cat r578/failures.md failed (file absent); bound SUMMARY already supplies stopped routes, and actual failures.json subsequently bound. No route was retried.'],'stopped_mechanisms':['321700 arbitrary monomial/generator and non-equigenerated scope ambiguity: no credit or proof investment','325693 recurrence equality does not supply blockwise exponent independence; no theorem or counterexample','324254 degenerate lambda=0 defect: wording correction only','No substantial computation, formalization, manuscript or broad repeated sweep undertaken'],'resource_limits':'All Python/helpers via fixed guard, python3 -B, OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1. Unchanged512MiB AS/groupRSS CPU210 wall230. No limit failures.'})
print('r304 matches',prior,'scope flags',sum(r['scope_flags']['restoration_required'] for r in out))
