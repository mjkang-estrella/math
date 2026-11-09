from pathlib import Path
import json,hashlib,collections,datetime
from fractions import Fraction
D=Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r699'
def dump(n,o): (D/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
a={}
for line in (D/'assessments.tsv').read_text().splitlines():
 i,c,q,r=line.split('\t');a[int(i)]=(c,q,r)
rows=json.loads((D/'literal-records.json').read_text());assert len(a)==50
out=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];c,q,reason=a[i]; known=i in [330063,333790]
 out.append({'mathdb_id':i,'corpus_chunk':x['chunk'],'corpus_line':x['line'],'exact_utf8_statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':x['canonical_record_sha256'],'classification':c,'classification_reason':reason,'quantifiers':q,'technical_assessment':reason,'disposition':'EXCLUDE_ALREADY_PROVED_IN_PRIMARY' if known else 'EXCLUDE_ROUTINE_DIRECTION_CORRECTION' if i==330506 else 'HOLD_SCOPE' if c!='complete' else 'PARK_NO_BOUNDED_FULL_SCOPE_ROUTE','source_url':r['source_url'],'primary_passage_read':i in [330063,333790,330506],'whole_body_read':False,'local_proof_body_read':known,'full_dependency_audit':False,'successor_body_clearance':False,'current_registry':'unavailable HOLD','prior_cleared':False,'accepted_credit':0})
dump('dispositions.json',out);dump('proposals.json',[])
# Executed bounded sanity checks; source proofs, not numerical checking, defeat eligibility.
V=[Fraction(1),Fraction(8)]
for n in range(1,100): V.append((8*n*(3*n*n+5*n+1)*V[n]-128*(n-1)*(n+1)**2*V[n-1])/(n*(n+1)**2))
assert all(V[n]**2>=V[n-1]*V[n+1] for n in range(2,100))
checks=[]
for s in range(1,21):
 f=[1]*(2*s+1)
 for n in range(s+1,2*s+1): f[n]=sum(f[n-j] for j in range(1,s+1))
 assert f[2*s]==2**(s-1)*(s-1)+1
 checks.append({'s':s,'count':f[2*s]})
assert 2**11>3**6
dump('bounded-checks.json',{'executed':True,'sequence':{'n_inequalities':[2,99],'first_values':[str(v) for v in V[:5]],'all_pass':True,'limit':'finite sanity only; no independent uniform proof'},'comb_recurrence':checks,'entropy_path3':{'degrees':[1,2,1],'H1':'3/2 log2','H2':'log3-1/3 log2','H1_greater_H2_equivalent':'2^11>3^6','left':2**11,'right':3**6,'route':'H prime(l)=-l Var_p(log d), classical Gibbs entropy derivative; no credit'}})
sp=[]
for i,ranges in [(330063,[(28,51),(69,95),(107,232)]),(333790,[(30,96),(246,258),(1077,1130)]),(330506,[(1186,1225),(1325,1364),(2913,2915)])]:
 lines=(D/(str(i)+'.txt')).read_text().splitlines()
 for lo,hi in ranges: sp.append({'mathdb_id':i,'text_file':str(D/(str(i)+'.txt')),'lines':[lo,hi],'text':'\n'.join(lines[lo-1:hi])})
dump('selected-passages.json',sp)
dump('source-coverage.json',{'literal_records_read':50,'classification_counts':dict(collections.Counter(e['classification'] for e in out)),'primary_documents_selected_passages':3,'local_proof_sections_read':[330063,333790],'source_definitions_and_question_read':[330063,333790,330506],'whole_bodies_read':0,'successor_bodies_read':0,'full_dependency_audits':0,'live_registry':'HOLD unavailable','successor_limit':'No target promoted. Source-internal proofs retire two; classical direction correction retires one. No novelty or successor clearance inferred.','routing_rows':10000,'baseline_literal_reviews':8383,'new_literal_reviews':50,'new_complete_statement_reviews':sum(e['classification']=='complete' for e in out),'acceptance':'zero; integrity does not imply mathematics or novelty PASS'})
f=json.loads((L/'sol-mathdb-primary-qualified-breadth-r696/failures.json').read_text());f['new_fetch_failures']=[];f['deviations']=['Initial full assigned metadata print was truncated; all50 statements subsequently read in three bounded batches.','Broad keyword locator output for three assigned primary documents was truncated and included adjacent theorem locators; subsequent reading restricted to relevant passage/proof ranges. No adjacent corpus statements read.','No whole source body, successor body, live registry or full dependency audit clearance. No hypothesis promoted.'];dump('failures.json',f)
# Flat originals only; no recursive historical expansion or corpus copies.
b=json.loads((D/'initial-bindings.json').read_text())['bindings']+json.loads((D/'context-bindings.json').read_text())
for e in json.loads((D/'source-provenance.json').read_text()):
 for k in ['pdf','text']:
  if k in e:b.append(e[k])
b={e['path']:e for e in b};dump('flat-bindings.json',list(b.values()))
print(collections.Counter(e['classification'] for e in out))
