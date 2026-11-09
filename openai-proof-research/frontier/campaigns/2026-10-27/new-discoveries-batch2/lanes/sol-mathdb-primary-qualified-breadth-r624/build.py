from pathlib import Path
import json,hashlib,datetime,collections
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r623'
def write(n,x):(D/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
rows={}
for s in (D/'reviews.tsv').read_text().splitlines():
 id,scope,dep,q,note=s.split('\t');rows[int(id)]=(scope,bool(int(dep)),q,note)
records=json.loads((D/'literal-records.json').read_text());assert len(rows)==len(records)==50
out=[]
for x in records:
 r=x['record'];id=r['mathdb_id'];scope,dep,q,note=rows[id]
 out.append({'mathdb_id':id,'corpus_chunk':x['chunk'],'corpus_line':x['line'],'literal_line_sha256':x['literal_line_sha256'],'canonical_record_sha256':x['canonical_record_sha256'],'exact_utf8_statement':r['statement'],'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'source_url':r['source_url'],'corpus_reported_completeness':r['statement_completeness'],'technical_statement_scope':scope,'complete':scope=='complete','incomplete':scope=='incomplete','definition_dependent':dep,'scope_ambiguous':scope=='scope-ambiguous','quantifiers_and_scope':q,'individual_disposition':note,'status':'HOLD_PRIOR_THEOREM_OBJECTION' if id==385797 else 'PARK_INFRASTRUCTURE' if id==385977 else 'HOLD_SOURCE_SCOPE' if scope!='complete' else 'PARK_NO_SMALL_FULL_SCOPE_ROUTE','record_statement_review':True,'primary_question_passage_read':False,'source_internal_results_read':id in [385797,386319],'whole_primary_body_read':False,'local_proof_read':id==385797,'full_dependency_audit':False,'closest_successor_body_clearance':False,'registry_clearance':False,'prior_cleared':False,'accepted_credit':0})
write('dispositions.json',out);write('proposals.json',[])
# Bounded arithmetic sanity checks, not research certificates.
checks={'executed':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'rbm_4_3':{'parameter_count':4*3+4+3,'simplex_dimension':2**4-1,'conclusion':'19>=15: parameter count does not refute universality; not proof of it'},'radial_ratio':{'dimensions_checked':list(range(1,10)),'denominators':[16*(n-10)*(n-14)*(n-18) for n in range(1,10)],'conclusion':'all nonzero; supplies no Fourier interpolation theorem'},'critical_multiplicity':{'formula':'weighted=sum m_c*h_c <= (2d-2)*sum h_c, since h_c>=0 and 1<=m_c<=2d-2','implication':'unweighted >= (c1*h_M-c2)/(2d-2) for each fixed d>=2; routine consequence of prior theorem','numerical_degree_checks':{str(d):2*d-2 for d in range(2,11)}},'finite_graph_sweep':'NOT EXECUTED: source 2-splittability definitions unavailable; no parameter sweep used to invent scope'}
assert all(checks['radial_ratio']['denominators']);write('bounded-checks.json',checks)
counts=dict(collections.Counter(x['technical_statement_scope'] for x in out))
write('source-coverage.json',{'literal_records_read':50,'technical_scope_counts':counts,'definition_dependent':sum(x['definition_dependent'] for x in out),'complete_statement_reviews':sum(x['complete'] for x in out),'incomplete_rows_replaced':0,'incomplete_rows_counted_as_complete':0,'primary_question_passages':0,'selected_prior_sources':2,'whole_bodies_read':0,'local_concluding_proof_read':1,'full_dependency_audits':0,'registry':'HOLD unavailable; zero MathDB requests','routing_metadata_review_credit':0,'proposals':0,'credit':0,'baseline':6533,'baseline_meaning':'reported literal reviews, not full technical corpus coverage','campaign_counts':{'additional':9,'total':39,'next':40}})
# Read complete bounded administrative exclusion lists and check direct ID overlap; these are not proof bodies.
ex=json.loads((L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json').read_text());hist=json.loads((L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text())
write('context-check.json',{'accepted_families':ex['accepted_family_count'],'historical_top_level_keys':list(hist),'r363':'364119 excluded routine published source counterexample; no reopening','r623_retired':[338290,339564,372627],'r623_parked':[337963,338408],'focused_protected':[338366,338408],'baseline':6533,'other_breadth_lane':'sol-mathdb-primary-qualified-breadth-r622','sol_r620':'completed/reconciled','promotions':0,'caution':'Administrative exclusions not independently audited mathematics.'})
print(counts)
