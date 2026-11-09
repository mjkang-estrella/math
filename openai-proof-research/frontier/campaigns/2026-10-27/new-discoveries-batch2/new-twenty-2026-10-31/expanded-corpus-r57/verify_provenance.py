from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent;root=Path('/home/mj-kang/Documents/Dev/math');sha=lambda x:hashlib.sha256(x).hexdigest();records=json.loads((p/'records.json').read_text());cache={}
for v in json.loads((p/'provenance.json').read_text()):
 path=root/v['chunk']
 if str(path) not in cache:
  raw=path.read_bytes();assert sha(raw)==v['chunk_sha256'];cache[str(path)]=raw.splitlines(keepends=True)
 line=cache[str(path)][v['line']-1];i=str(v['id']);assert line.endswith(b'\n');assert line==(p/'raw'/(i+'.jsonl')).read_bytes();assert sha(line)==v['raw_sha256'];d=json.loads(line);assert d==records[i];assert sha(d['statement'].encode())==v['statement_sha256']
results=json.loads((p/'results.json').read_text());assert len(results)==40;assert set(results)==set(map(str,json.loads((p/'reservation.json').read_text())['ids']));assert all(x['accepted_credit']==0 for x in results.values())
print('PASS: 40 exact newline-preserving raw rows, full chunk and literal hashes, exact result keys, zero credit.')
