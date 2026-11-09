from pathlib import Path
import json,hashlib,math
from fractions import Fraction
D=Path(__file__).parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r605';B=L.parent
load=lambda p:json.loads(p.read_text())
def save(n,v):(D/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
a=load(I/'active-breadth-reservations.json');cov=load(I/'coverage-delta.json');q=load(I/'queue-r606.json');ids={r['mathdb_id'] for r in q};assert len(ids)==50 and len(cov)==6133
allsets=[set(x['ids']) for x in a];print([(x['lane'],len(x['ids']),x['status']) for x in a])
for j,s in enumerate(allsets):
 assert not s & {int(x) for x in cov}
 assert not s & ({343771,343973,344924,383181}|set(a[j]['protected_ids']))
 for z in allsets[:j]:assert not s&z
assert ids==set(load(I/'reserved-ids-r606.json')['ids'])
notes={}
for s in (D/'review-notes.tsv').read_text().splitlines():
 i,c,qu,n=s.split('\t');notes[int(i)]=(c,qu,n)
assert set(notes)==ids
primary={348407:('projective.txt','arXiv:2010.10762v1','Sections2-4, especially Proposition4.9,Conjecture4.10 and printed random-coding bound; no full dependency audit'),348200:('msrd.txt','arXiv:2010.02779v1','Definition6.4,Theorem6.5 proof,Corollary6.6,Conjecture6.8; no all-block proof'),348418:('howroyd.txt','arXiv:2010.11112v2','Conjecture1.1,Theorem2.1 statement and opening proof,Section4 theorem pointers; not entire proof'),351985:('vincular.txt','arXiv:2109.09183v1','Section6 merge example,Theorem6.6 proof excerpt,Conjecture6.7 and expectation interpretation; not full body')}
dis=[]
for x in load(D/'literal-records.json'):
 r=x['record'];i=r['mathdb_id'];c,qu,n=notes[i]
 dis.append({'mathdb_id':i,'title':r['title'],'corpus_chunk':x['chunk'],'corpus_line':x['line'],'statement_utf8':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':x['canonical_record_sha256'],'metadata_completeness':r['statement_completeness'],'statement_scope':c,'complete_mathematical_statement_review':c=='complete','literal_record_reviewed':True,'quantifiers_reviewed':qu,'technical_disposition':n,'disposition':'STOP_SOURCE_SUBSUMPTION_RISK' if i==348407 else 'EXCLUDE_DOMAIN_CORRECTION' if i in [349246,351732] else 'HOLD_DEFINITION_SOURCE' if c=='incomplete' else 'PARK_NO_SMALL_FULL_SCOPE_ROUTE','primary_source_url':r['source_url'],'source_passage':primary.get(i,None),'whole_body_read':False,'local_proof_established':i==348407,'full_dependency_audit':False,'successor_body_clearance':False,'current_registry':'HOLD unavailable; no absence-of-hits inference','novelty_cleared':False,'discovery_credit':0})
save('dispositions.json',dis);save('proposals.json',[])
counts={'literal_records_reviewed':50,'complete_mathematical_statements_reviewed':sum(x['complete_mathematical_statement_review'] for x in dis),'incomplete_or_definition_dependent':sum(not x['complete_mathematical_statement_review'] for x in dis),'selected_primary_passages':4,'whole_bodies_audited':0,'full_dependency_audits':0,'proposals':0,'credit':0,'baseline_reported_literal_reviews':6133,'routing_metadata_rows':8000,'routing_extra_review_credit':0,'reservation_disjointness':'PASS all active sets, baseline6133, protected and four restoration ids'}
save('source-coverage.json',{'counts':counts,'primary':primary,'prior':{'file':'prior.txt','version':'arXiv:1201.6043v2','scope':'Section2 known-bound passage inspected; it gives fixed-rate asymptotic random-coding context, not the exact fixed-codimension bridge needed here'},'successors':'No relevant successor body cleared; bounded search did not supply one. No promotion.','registry':'Unavailable HOLD','proof_scope':'Exact elementary optimizer comparison only, not an audit of coding-theory dependencies.'})
# Reconcile actual administrative objects after binding; preserve matched entries only, not historical trees.
def hits(v,path=''):
 out=[]
 if isinstance(v,dict):
  if any(v.get(k) in ids for k in ['mathdb_id','mathdb_related_id']):out.append(v)
  for k,z in v.items():out+=hits(z,path+'/'+k)
 elif isinstance(v,list):
  for z in v:out+=hits(z,path)
 return out
save('prior-context-check.json',{'counts':{n:len(load(B/n).get('accepted',[])) for n in ['ledger.json','prior-campaign-context.json']},'assigned_id_matches':{str(p):hits(load(p)) for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',B/'ledger.json',B/'prior-campaign-context.json']},'r363':'Cayley364119 excluded: source already contains literal negation; preserve analogous substantive exclusion discipline.','r605':'337963 parked;338290,339564,372627 retired; all protected excluded from reservation.'})
t=8;coef=Fraction(1,2**t*math.factorial(t+1))*math.prod(Fraction(2**j-1,2**j) for j in range(1,t+1));candidate=Fraction(1,9**9)
checks=load(D/'bounded-checks.json');checks.append({'check':'printed random-coding leading coefficient t8','coefficient':str(coef),'conjectured_coefficient':str(candidate),'ratio':str(coef/candidate),'strictly_better':coef>candidate,'obligation':'Use j=t+1 summand, fixed t and k->infinity; Proposition4.9 supplies conjectured upper asymptotic if optimizer claim true.'})
bases=math.prod(128-2**j for j in range(7));assert bases%math.factorial(8)==0
checks.append({'check':'integer uniform t7 k1016','F_all127_weights8':bases//math.factorial(8)*8**8,'F_eight_weights127':127**8,'strictly_better':bases//math.factorial(8)*8**8>127**8})
save('bounded-checks.json',checks)
save('failures.json',{'failed_integrity_checks':[],'failed_http_requests':[],'stopped_routes':[{'id':348407,'reason':'Uniform lower t2..6 does not beat optimizer; succeeds at7, but older random-coding bound printed in same source already defeats universal implication at8. Smaller witness not separate credit.'},{'id':348200,'reason':'Definition restored but larger-weight alternating terms obstruct a one-weight convexity shortcut; no sweep.'},{'id':348418,'reason':'Residue-zero case already proved; full two-residue classification not available.'},{'id':351985,'reason':'Aggregated variance theorem does not establish per-overlap inequality; endpoint wording defects excluded.'}],'access_holds':['MathDB429: zero direct requests','current proof registry unavailable','AIM/Kourovka/EGRES/AIProofWatch parked','DMGT TLS/ProjectEuclid challenge/ResearchGate403 parked','OEIS A274199/internal403 parked; not retried'],'deviations':['A public web search returned an incidental MathDB indexed snippet. No MathDB URL was opened, requested directly, or used as evidence.','Initial literal-record display exceeded tool output cap; all50 statements were subsequently read in three bounded untruncated displays.'],'scope_limits':['No novelty PASS','No entire primary proof-body audit','No Lean or manuscript changes','No substantial hypothesis delegated']})
print(counts);print('random ratio',coef/candidate)
