from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
for p in L.rglob('*'):
 if p.is_file() and (p.suffix in ['.olean','.ilean','.c','.o','.ir'] or '.olean.' in p.name):p.unlink()
attempts=[]
for p in sorted(L.glob('attempt-*.json')):
 d=json.loads(p.read_text());d['receipt']=p.name;d['panic_in_log']='PANIC' in p.with_suffix('.log').read_text();attempts.append(d)
(L/'provenance.json').write_text(json.dumps(dict(date='2026-10-30',status='PARTIAL geometric prototype; novelty HOLD; no acceptance',counts=[9,39,40],source_bindings='source-bindings.json',mathlib_bindings='mathlib-bindings.json',attempts=attempts,network_requests=0,scope_writes='assigned lane only',source_claim=False,children=0),indent=2)+'\n')
manifest={str(p.relative_to(L)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
(L/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');print('manifest written:',len(manifest),'files')
