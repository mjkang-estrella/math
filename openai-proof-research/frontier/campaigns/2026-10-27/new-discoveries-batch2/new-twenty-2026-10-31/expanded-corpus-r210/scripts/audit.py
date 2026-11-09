from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1];r=json.loads((L/'results.json').read_text());res=json.loads((L/'reservation.json').read_text());assert len(r)==20 and set(r)==set(map(str,res['ids']))
for k,v in r.items():
 b=(L/'sources'/f'{k}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==v['provenance']['raw_sha256'];d=json.loads(b);assert d['statement']==v['literal_statement'];assert hashlib.sha256(d['statement'].encode()).hexdigest()==v['statement_sha256'];assert v['credit']==0 and v['lean_endpoint'] is None
processes={}
for p in (L/'outputs').glob('*-resource.json'):
 d=json.loads(p.read_text());assert d['returncode']==0;processes[p.name]=d
assert len(processes)==8,len(processes)
manifest={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['artifact-manifest.json','final-audit.json']}
(L/'outputs/artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(L/'outputs/final-audit.json').write_text(json.dumps({'reserved_records':20,'unique_result_keys':20,'raw_line_and_statement_hashes':'PASS','claimed_credit':0,'lean_packet':False,'successful_capped_processes':processes,'artifact_count':len(manifest)},indent=2)+'\n')
print('PASS: 20 exact records, provenance hashes, zero credit, 8 successful capped processes; artifacts',len(manifest))
