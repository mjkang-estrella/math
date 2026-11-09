from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;L=R.parent
J=lambda p:json.loads(p.read_text())
def put(n,o):(R/n).write_text(json.dumps(o,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
records=J(R/'records.json');assigned=J(L/'root-mathdb-breadth-intake-r443/reserved-ids.json');baseline=J(L/'root-mathdb-breadth-intake-r443/coverage-delta.json')
assert len(baseline)==2483
ids={x['mathdb_id'] for x in records};assert ids==set(assigned['ids']) and len(ids)==50
assert not ids&set(assigned['other_active_reservations']) and not set(map(str,ids))&set(baseline)
assert not ids&{372627,372628,368940,404067,364119}
admin=L/'root-mathdb-accepted-exclusions-r304'
accepted=J(admin/'accepted-exclusions.json');history=J(admin/'historical-dispositions.json')
# No unassigned records are displayed. Administrative join is not technical review.
def hits(obj):
 if isinstance(obj,dict):
  if obj.get('mathdb_id') in ids:return [obj]
  return [h for v in obj.values() for h in hits(v)]
 if isinstance(obj,list):return [h for v in obj for h in hits(v)]
 return []
put('administrative-reconciliation.json',{'accepted_assigned_hits':hits(accepted),'historical_assigned_hits':hits(history),'accepted_family_count':accepted['accepted_family_count'],'baseline_distinct_reported_reviews':len(baseline),'other_active_reservations':len(assigned['other_active_reservations']),'r363_rule':'364119 source-known negation; no credit for smaller witness','counts':{'additional':9,'total':39,'next':40},'not_a_live_registry':True})
# Exact bounded dead-shortcut check, not a proposed result.
solutions=[(a,b) for a in range(4) for b in range(4) if (a+b)%4==0 and (a*a+b*b)%4==0]
assert (0,0) in solutions and (2,2) in solutions
put('bounded-check.json',{'mathdb_id':401135,'executed':True,'n':2,'N':4,'target':[0,0],'residue_solutions':solutions,'conclusion':'permutation-only shortcut fails at a composite modulus; no full-scope claim','certificate_size':'two coordinates for the extra residue tuple; exhaustive check of 16 ordered pairs','planned_check':'primary source counting convention and meaningful closed formula; not executed'})
sections={
'401139':('15578',580,605),'401166':('15580',654,703),'401169':('15580',1080,1164),'401371':('15957',860,950),'401376':('15957',1290,1343),'401602':('16164',1343,1380),'401603':('16164',1640,1775),'401605':('16164',1640,1775),'401894':('16627',802,877)}
excerpts=[]
for n,(f,a,b) in sections.items():
 lines=(R/'sources'/(f+'.txt')).read_text().split('\n')
 excerpts.append({'mathdb_id':int(n),'text_path':'sources/'+f+'.txt','lines_inclusive':[a,b],'excerpt':'\n'.join(lines[a-1:b]),'scope':'relevant section only; complete downloaded report is not claimed read'})
s=(R/'sources/spheres.txt').read_text().split('\n')
excerpts.append({'mathdb_id':401139,'text_path':'sources/spheres.txt','lines_inclusive':[1068,1165],'excerpt':'\n'.join(s[1067:1165]),'scope':'concluding proof section read; surgery/gluing dependency closure not audited','version':'live author PDF retrieved in this run; no immutable arXiv version asserted'})
put('source-excerpts.json',excerpts)
assess={}
for line in (R/'assessments.tsv').read_text().splitlines():
 n,d,scope,reason=line.split('\t');assess[int(n)]=(d,scope,reason)
assert set(assess)==ids
rows=[]
for x in records:
 n=x['mathdb_id'];d,scope,reason=assess[n];has=str(n) in sections
 rows.append({'mathdb_id':n,'title':x['title'],'canonical_url':x['canonical_url'],'source_url':x['source_url'],'source_name':x['source_name'],'literal_statement':x['statement'],'literal_statement_sha256':sha(x['statement'].encode()),'canonical_record_sha256':sha(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()),'disposition':d,'scope':scope,'reason':reason,'record_statement_level':'full_literal_read','primary_level':'relevant_primary_section_read' if has else 'not_read_primary_fidelity_HOLD','proof_level':'concluding_proof_read_dependency_closure_not_audited' if n==401139 else ('source_reports_prior_proof_body_not_read' if n in [401166,401169,401602] else 'no_full_scope_proof_read'),'registry_level':'HOLD_current_registry_not_checked','source_excerpt_indices':[i for i,e in enumerate(excerpts) if e['mathdb_id']==n],'current_open_status':'not_independently_verified','decisive_check':'bounded-check.json' if n==401135 else 'statement/primary-scope comparison only; no computation executed','certificate_size':'none proposed','formal_dependencies':'no formalization undertaken; no full-scope route qualified','prior_clearance':False,'discovery_credit':0})
put('dispositions.json',rows);put('proposals.json',[])
put('failures.json',{'preserved_helper_failures':['preflight-failure-1.log','preflight-failure-2.log'],'source_failures':[x for x in J(R/'pdf-provenance.json') if 'failure' in x],'MathDB_requests':0,'MathDB_429':'inherited HOLD; no requests attempted','inherited_parked_routes':['denied AIM','denied Kourovka','denied EGRES','AIProofWatch 403','rigid-body/triangle-gap successor 403'],'current_registry':'HOLD: no current head or proof registry body obtained; no hypothesis promoted','scope_limits':['41 assigned primary bodies not read','one concluding external proof section read; no dependency closure audit','no complete successor/version/prior-art clearance for any proposal'],'network_discipline':'no 403/429 encountered by this lane; no retry of matching 404; no barred routes used'})
put('search-provenance.json',{'tool':'web search','queries':['maximum matching FPC Anderson Dawar Holm 2013 definable linear programming','2 convex embedded spheres path connected Buzano Haslhofer Hershkovits','Ramsey equivalence clique star Kk t(k) Szabo Zumstein Zurcher'],'purpose':'identify historical theorem/proof-body leads, not registry clearance','primary_leads':['https://arxiv.org/abs/1607.05604','https://arxiv.org/abs/1304.6870','https://www.math.utoronto.ca/roberth/papers/buzanohaslhoferhershkovits.pdf','https://pages.cs.wisc.edu/~mwa/research/papers/adh13.pdf'],'barred_search_results':'ScienceDirect results not opened or relied upon','date':'2026-10-31'})
print('BUILT',len(rows),'records;',len(sections),'primary relevant sections; proposals 0')
