import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];h=lambda b:hashlib.sha256(b).hexdigest()
R=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(R)==20 and set(R)==set(map(str,ids))
for i,v in R.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n') and h(b)==v['provenance']['raw_sha256'];row=json.loads(b);assert row['mathdb_id']==int(i) and row['statement']==v['literal_statement'];assert h(row['statement'].encode())==v['provenance']['statement_sha256'];assert v['discovery_credit']==0 and not v['self_accepted'] and v['lean_endpoint'] is None
 src=(D/v['source_pdf']).read_bytes();assert h(src)==v['source_pdf_sha256']
assert (D/'SUMMARY.md').exists()
assert json.loads((D/'outputs/digraph-exact.json').read_text())['normalized_matrices_checked']==1850000
assert json.loads((D/'outputs/digraph-pruned-7.json').read_text())['completed_matrices']==887627
assert json.loads((D/'outputs/safe-extended-13-5.json').read_text())['disk_extension_tests']==5460
assert len(json.loads((D/'outputs/cycles.json').read_text()))==206
assert not json.loads((D/'outputs/dyck.json').read_text())['anomalies']
# Bind completed artifacts; this validator's active log/receipt are intentionally excluded.
files={}
for p in D.rglob('*'):
 if not p.is_file() or '/vendor/' in str(p) or '/__pycache__/' in str(p):continue
 rel=str(p.relative_to(D))
 if rel in ['manifest.json','validation.json','logs/validate.log','logs/validate.receipt.json']:continue
 files[rel]={'bytes':p.stat().st_size,'sha256':h(p.read_bytes())}
(D/'manifest.json').write_text(json.dumps(files,indent=2)+'\n')
result={'reserved_ids':20,'result_entries':20,'raw_newlines_and_hashes_verified':20,'literal_statements_verified':20,'current_source_pdf_hashes_verified':20,'manifest_artifacts':len(files),'new_solutions_nominated':0,'Lean_invocations':0,'self_acceptance':False,'manifest_exclusions':['validator active log/receipt','validation.json','manifest.json itself','extracted NetworkX source and bytecode; source ZIP separately hash-bound'],'scope':'artifact consistency, not independent mathematical certification'}
(D/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
