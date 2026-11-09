import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parent
rows=json.loads((D/'assigned-records.json').read_text());a={}
for l in (D/'assessments.tsv').read_text().splitlines():
 i,s,n=l.split('\t',2);a[int(i)]=(s,n)
assert set(a)=={r['mathdb_id'] for r in rows} and len(a)==50
out=[]
for r in rows:
 i=r['mathdb_id'];s,n=a[i];p={395938:('sol-mathdb-primary-qualified-breadth-r428/sources/4080.txt',1875,1929,'2064-2065'),398787:('sol-mathdb-primary-qualified-breadth-r436/sources/12861.txt',2371,2490,'57-60'),400959:('sol-mathdb-primary-qualified-breadth-r442/sources/owr2017-20.txt',1650,1748,'1245-1246')}.get(i)
 out.append({k:r[k] for k in ['mathdb_id','chunk','line','statement','statement_sha256','canonical_record_sha256']}|{'source_url':r['record']['source_url'],'disposition':s,'technical_reading':n,'literal_statement_read':True,'primary_passage_read':bool(p),'primary_passage':None if not p else {'path':str(D.parent/p[0]),'start_line':p[1],'end_line':p[2],'printed_pages':p[3]},'whole_primary_body_read':False,'local_proof_established':False,'full_dependency_audit':False,'successor_proof_body_read':False,'current_registry':'HOLD unavailable; zero MathDB requests; no absence-of-hits inference','source_scope_cleared':False,'prior_cleared':False,'accepted_credit':0})
(D/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(D/'proposals.json').write_text('[]\n')
coverage={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':D.name,'baseline_reconciled_literal_reviews':4533,'assigned_literal_statements_read':50,'arithmetic_baseline_plus_lane':4583,'integration_status':'root reconciliation pending; no shared coverage edited','primary_passage_rows':[395938,398787,400959],'whole_primary_bodies_read':0,'successor_proof_bodies_read':0,'full_dependency_audits':0,'proposals':0,'credit':0,'registry':'HOLD','mathdb_requests':0,'network':'Three successful EMS article metadata HTML GETs; no challenge/403/429; no PDF downloaded, extracted or rendered in this lane. Existing immutable PDF/text pairs reused after manifest checks.','scientific_gate':'No math/novelty PASS','counts':'9 additional / 39 total / next 40 unchanged'}
(D/'coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
# Retain precisely the inspected passages with independent hashes, without copying whole source trees.
ex=[]
for d in out:
 if d['primary_passage']:
  p=d['primary_passage'];lines=pathlib.Path(p['path']).read_text().splitlines(keepends=True);t=''.join(lines[p['start_line']-1:p['end_line']]);ex.append({'mathdb_id':d['mathdb_id'],**p,'text':t,'utf8_sha256':hashlib.sha256(t.encode()).hexdigest()})
(D/'source-excerpts.json').write_text(json.dumps(ex,ensure_ascii=False,indent=2)+'\n')
