from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r491'
def load(p):return json.loads(p.read_text())
def out(n,o):(D/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
A={}
for l in (D/'assessments.tsv').read_text().splitlines():
 i,s,r=l.split('\t',2);A[int(i)]=(s,r)
rows=load(D/'assigned-records.json');assert len(A)==50 and set(A)=={x['record']['mathdb_id'] for x in rows}
source_ids={'2109.00722':[351811],'2109.03129':[351862],'2110.04263':[352158],'2110.10515':[352312,352313],'2111.12282':[352729],'2112.15551':[353146],'2202.09822':[353677],'2203.02457':[353822],'2203.07222':[353915,353917],'2112.09396':[352960],'2202.07746':[353643],'2110.14716':[352392]}
ps={i:a for a,ii in source_ids.items() for i in ii}
disp=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];s,reason=A[i]
 disp.append({'mathdb_id':i,'literal_statement':r['statement'],'original_chunk':x['chunk'],'original_line':x['line'],'statement_utf8_sha256':sha(r['statement'].encode()),'canonical_record_sha256':sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'canonical_url':r['canonical_url'],'source_url':r.get('source_url'),'disposition':s,'reason':reason,'evidence_levels':{'literal_statement_read':True,'selected_primary_passages_read':i in ps,'whole_primary_body_read':False,'selected_proof_body_read':i in {351811,352158,352960,353146,353677,353822},'complete_dependency_audit':False,'current_registry_cleared':False},'primary_evidence':('sources/'+ps[i]+'.txt; source-review.md') if i in ps else None,'duplicate_prior_status':'Public full-scope theorem in retained primary' if s=='EXCLUDE_PUBLIC_THEOREM' else 'Reported resolved; no primary replay here' if s=='EXCLUDE_REPORTED_PUBLIC' else 'Uncleared; no absence-of-hits novelty inference','accepted_credit':0})
out('dispositions.json',disp)
out('proposals.json',{'qualified_briefs':[],'count':0,'new_proposed_proofs':0,'accepted_credit':0,'reason':'No candidate has both source-qualified surviving full scope and a concrete complete mechanism. No substantial new proof attempt or promotion; closest successor bodies and current registry not cleared.'})
out('coverage-provenance.json',{'baseline_reported_reviews':3533,'assigned_ids':sorted(A),'new_literal_reviews':50,'reported_review_total_if_root_reconciles':3583,'selected_primary_passages':14,'retained_primary_pdfs':12,'whole_primary_body_reviews':0,'selected_complete_proof_body_readings':6,'partial_proof_body_readings':[353643],'complete_dependency_audits':0,'registry_clearances':0,'automated_tags_count_as_reviews':False,'accepted_additional':9,'accepted_total':39,'next':40,'root_reconciliation_required':True,'compliance_deviation':'Unrelated historical descriptions displayed from administrative ledgers after binding; not investigated or counted.'})
out('failures.json',{'events':[{'kind':'scope_display_deviation','detail':'cat of ledger.json and prior-campaign-context.json produced truncated administrative output containing unrelated unassigned historical result descriptions. This was after flat binding; no mathematical investigation, reuse, or coverage claimed for them. Integrity PASS cannot repair this deviation.'},{'kind':'truncated_read','detail':'Two broad source-label rg outputs and administrative cat were truncated. Complete assigned literal statement file was subsequently read in bounded nontruncated ranges. Source claims restricted to explicitly read passages.'},{'kind':'nonzero_search','detail':'A batched rg for polynomial/Conjecture 5 in retained 2112.15551 returned exit 1 (no matching text); not evidence of novelty or disproof. Version/scope remains HOLD.'}], 'access_failures':load(D/'source-access-failures.json'),'registry':'HOLD: no current registry acquired; no retries or alternate routes. MathDB 429 HOLD inherited, zero MathDB requests. All named blocked routes remain parked.','resource_failures':[]})
out('adjudications-carried.json',load(I/'adjudications.json'))
refs=load(D/'flat-bindings.json')
for e in load(D/'source-provenance.json'):
 for role in ['pdf','text']:
  refs.append({'path':e[role],'size':e[role+'_size'],'sha256':e[role+'_sha256'],'kind':'bound-primary-'+role})
out('flat-bindings.json',refs)
# Match assigned IDs only, without displaying or copying unrelated historical entries.
hits=[]
def walk(o,p):
 if isinstance(o,dict):
  exact=[i for i in A if str(i) in o or o.get('mathdb_id',o.get('problem_id'))==i]
  if exact:hits.append({'file':p,'ids':exact,'note':'Exact key or ID-field hit; no automatic semantic exclusion inference'})
  for v in o.values():walk(v,p)
 elif isinstance(o,list):
  for v in o:walk(v,p)
for n in ['accepted-exclusions.json','historical-dispositions.json']:walk(load(L/'root-mathdb-accepted-exclusions-r304'/n),n)
out('history-assignment-check.json',{'assigned_exact_key_or_id_hits':hits,'scope':'Only exact assigned IDs screened in already bound r304 administrative history. No unrelated historical proofs reviewed. Semantic global novelty not cleared.'})
print('built',len(disp),'dispositions;',len(ps),'primary passage records; historical exact hits',hits)
