import pathlib,json,hashlib,datetime,collections
L=pathlib.Path(__file__).resolve().parent;B=L.parent
D=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest()
notes={int(i):(s,t) for i,s,t in (a.split('\t',2) for a in (L/'assessment.tsv').read_text().splitlines())}
assert len(notes)==50
partial={403185,403280,403424,403542,403623,403626,403636,403663}
rows=[]
for x in D(L/'assigned-records.json'):
 r=x['record'];i=r['mathdb_id'];status,note=notes[i];page=int(r['source_name'].rsplit('page ',1)[1]);sid=r['source_url'].rsplit('/',1)[1]
 extra={403194:[19,20],403480:[48],403481:[56,57,58,59],403510:[24],403517:[14],403519:[9,10],403614:[22],403626:[13],403629:[17,18],403655:[38,39],403663:[36]}.get(i,[])
 successor={'status':'HOLD: no current proof-registry clearance; cited references are leads, not full proof-dependency review','scope_matched_public_resolution_verified':False,'proof_body_read':False}
 if i==403560:
  successor.update(body='sources/arxiv-2309.04460.txt',sections='Introduction and Theorem 1.1, PDF pages 1-2',finding='2025 v2 gives average degree C log n log log n, not O(log n). The other retrieved short-cycle paper 2311.12302 concerns color-class hypotheses and is not the same extremal statement.',status='closest retrieved successor inspected; further successors/current registries HOLD')
 if i==403432:
  successor.update(body='sources/arxiv-2206.02689.txt',sections='Introduction Theorems A,B, PDF pages 1-2',finding='Constructs a Quillen pair; explicitly conjecturally an equivalence. This does not resolve all n>2.',status='closest retrieved successor inspected; further successors/current registries HOLD')
 rows.append(dict(mathdb_id=i,title=r['title'],statement=r['statement'],statement_utf8_sha256=H(r['statement'].encode()),canonical_record_sha256=x['canonical_record_hash'],canonicalization='UTF-8 JSON, ensure_ascii=False, sort_keys=True, separators=(comma,colon)',original_chunk=x['original_chunk'],original_line=x['original_line'],source_url=r['source_url'],source_name=r['source_name'],disposition=status,technical_disposition=note,accepted_credit=0,statement_quantifiers_read=True,source_evidence_level='primary report question and local results; definitions partial' if i in partial else 'primary report question and local results; no full proof-dependency review',primary_section=dict(file='sources/ems-'+sid+'.txt',cited_pdf_page=page,additional_pdf_pages=extra,question_located=True,definition_coverage='partial' if i in partial else 'local report context',source_internal_results_read='local results only',full_primary_proof_dependencies_read=False),successor_review=successor,bounded_check=dict(mathematical_computation_executed=False,status='not attempted; parked after statement/primary-source screen',integrity_computation='guarded hashing, streaming extraction and assignment verification only',finite_instance_credit=False),remaining_obstacle=note,prior_gaps=['Current proof registries not cleared; inherited forbidden routes remain HOLD.','Full source-internal proof dependencies and full successor bibliography not read.'],hypothesis_brief=False))
assert len(rows)==50
(L/'dispositions.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n');(L/'proposals.json').write_text('[]\n')
source_files=[]
for p in sorted((L/'sources').iterdir()):
 b=p.read_bytes();source_files.append({'file':str(p.relative_to(L)),'bytes':len(b),'sha256':H(b)})
(L/'source-provenance.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'access_records':['source-access.json','pdf-access.json','successor-access.json','focused-access.json','exact-access.json','successor-bodies-access.json'],'files':source_files,'extraction':'pdftotext -layout via guarded Python subprocess; no layout-dependent numerical inference','mathdb_requests':0,'forbidden_routes_attempted':0,'public_uploads':0},indent=2)+'\n')
(L/'source-review.json').write_text(json.dumps({'statement_count':50,'primary_report_question_located':50,'primary_definition_context_partial_ids':sorted(partial),'full_proof_dependency_reviews':0,'successor_theorem_sections_read_ids':[403432,403560],'current_registry_clearance':False,'not_novelty_evidence':'Empty searches, MathDB open labels and empty solutions arrays are not used as novelty evidence.','report_internal_examples_not_new':[403258,403378,403481,403510,403572,403613,403615],'successor_limits':'Searches were bounded and neither exhaustive nor uniformly scoped across all fifty. All unresolved successor/registry checks remain HOLD.'},indent=2)+'\n')
print(collections.Counter(r['disposition'] for r in rows))
