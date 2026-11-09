from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'results.json').read_text());reserved=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==40 and set(map(int,r))==set(reserved)
chunks={}; checks=[]
for i,o in r.items():
 p=o['provenance'];f=Path(p['chunk'])
 if f not in chunks:
  b=f.read_bytes();assert sha(b)==p['chunk_sha256'];chunks[f]=b.splitlines(keepends=True)
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b==chunks[f][p['line_1based']-1];assert sha(b)==p['raw_sha256'];assert b.endswith(b'\n');assert sha(o['statement'].encode())==p['statement_utf8_sha256'];assert json.loads(b)['statement']==o['statement']
 assert o['credit']==0 and o['formal_endpoint_complete'] is False
 checks.append(i)
for f in (D/'sources').glob('*.receipt.json'):
 a=json.loads(f.read_text())
 if 'sha256' in a:assert sha(Path(a['path']).read_bytes())==a['sha256']
counts={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_entries':len(r),'raw_bindings_pass':len(checks),'distinct_chunks':len(chunks),'distinct_arxiv_urls':len({a['source_url'] for a in r.values()}),'source_statuses':{s:sum(str(o['primary_status'])==s for o in r.values()) for s in {str(o['primary_status']) for o in r.values()}},'credit':0,'Lean_endpoint':False,'ordinary_candidate':'365710','not_claimed':'Mathematical proof validation, global novelty, Lean replay or campaign acceptance'}
(D/'outputs/validation.json').write_text(json.dumps(counts,indent=2)+'\n')
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in sorted(D.rglob('*')) if p.is_file() and p.name!='manifest-sha256.json' and '__pycache__' not in str(p)}
(D/'manifest-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(counts,indent=2))
