from pathlib import Path
import json,hashlib,re,datetime,collections
L=Path(__file__).parent
H=lambda b:hashlib.sha256(b).hexdigest()
load=lambda s:json.loads((L/s).read_text())
# Corrected locator packet; pre-existing sources already pinned before reading.
exec(compile((L/'primary.py').read_text().replace("int(sys.argv[1])<=i<int(sys.argv[2])","False"),'local-primary','exec'))
passages={r['source']:r for r in load('read-primary-passages.json')}
extra=[]
for aid,a,b in [('0912.1150',270,295),('0907.1583',88,104),('1003.5632',133,168),('0809.4627',875,920),('0808.3760',706,745),('0901.3945',164,227)]:
 p=L/'sources'/f'{aid}.txt';ls=p.read_text().split('\n');extra.append({'source':aid,'start_line':a,'end_line':b,'passage':'\n'.join(f'{i}: {ls[i-1]}' for i in range(a,b+1)),'scope':'selected passage; not full proof audit'})
(L/'supplemental-passages.json').write_text(json.dumps(extra,ensure_ascii=False,indent=2)+'\n')
ass={}
for line in (L/'assessment.tsv').read_text().splitlines():
 i,s,t=line.split('\t');ass[int(i)]=(s,t)
checks=load('bounded-checks.json');sources=load('source-provenance.json')
for r in sources:
 text=Path(r['path']).with_suffix('.txt').read_text();aid=r['source_url'].rsplit('/',1)[-1]
 m=re.search(r'arXiv\s*:\s*'+re.escape(aid)+r'v\d+',text,re.I)
 r['version']=m.group(0) if m else 'revision label not recovered; unversioned arXiv PDF response pinned by SHA256 and retrieval UTC'
 r['read_status']='selected primary question/result passage read; see read-primary-passages.json; not full body or proof/dependency audit'
 r['source_internal_results_status']='only adjacent/selected results read; broader dependency and companion review incomplete'
 r['closest_successors_status']='HOLD: not comprehensively inspected; named leads in disposition are not clearance'
 r['status']='primary_selected_passage_read'
(L/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
out=[]
for v in load('assigned-records.json'):
 x=v['record'];i=x['mathdb_id'];aid=x['source_url'].rsplit('/',1)[-1];s,t=ass[i]
 out.append({'mathdb_id':i,'title':x['title'],'canonical_url':x['canonical_url'],'literal_statement':x['statement'],'statement_utf8_sha256':H(x['statement'].encode('utf-8')),'canonical_record_sha256':v['canonical_record_sha256'],'raw_line_sha256':v['raw_line_sha256'],'original_chunk':v['original_chunk'],'original_line':v['original_line'],'disposition':s,'full_scope_mechanism_or_obstacle':t,'review_level':'full literal statement and quantifiers read; selected primary passage read; definition/proof/dependency audit incomplete','primary_source':next(r for r in sources if r['source_url']==x['source_url']),'primary_passage':passages[aid],'source_evidence_level':'P1: actual selected primary question/result passage; no whole-body audit','proof_evidence_level':'exact routine literal counterexample only, no discovery credit' if str(i) in checks else 'P0: no new full-scope proof/counterexample certified','registry_evidence_level':'HOLD: no current proof-registry head or exact-scope clearance; MathDB 429 embargo and inherited denied routes respected','bounded_check':checks.get(str(i),{'status':'not executed','reason':'no bounded test would decide the universal statement with available audited definitions'}),'decisive_next_check': 'Already executed routine literal check; do not promote or repair scope for credit.' if str(i) in checks else 'Before investment: inspect exact definitions, relevant source internal proof/results and closest successor bodies; resolve the concrete gap in full_scope_mechanism_or_obstacle. No calculation or proof promised as completed.','expected_certificate_size':'routine finite witness recorded in bounded-checks.json; not eligible' if str(i) in checks else 'unknown; no complete small certificate identified','formal_dependencies':'No Lean run. Exact domain definitions and indicated structural theorem would need formalization; no endpoint claimed.','strongest_objection':t,'prior_gaps':'Live registry, companion-paper and successor proof/subsumption checks incomplete. No novelty inference from open labels, empty solutions, or missing hits.','discovery_credit':0,'proposal':False})
assert len(out)==50 and set(ass)=={v['mathdb_id'] for v in out}
(L/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(L/'proposals.json').write_text('[]\n')
print(collections.Counter(x['disposition'] for x in out))
