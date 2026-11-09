from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent;P=json.loads((O/'provenance.json').read_text());R=json.loads((O/'records.json').read_text());h=lambda d:hashlib.sha256(d).hexdigest();cache={}
for i,p in P.items():
 name=p['chunk']
 if name not in cache:cache[name]=Path(name).read_bytes()
 data=cache[name];line=data.splitlines(keepends=True)[p['one_based_line']-1];x=json.loads(line)
 assert h(data)==p['chunk_sha256'] and h(line)==p['raw_sha256'] and h(x['statement'].encode())==p['statement_sha256']
 assert x==R[i] and line==(O/'raw'/f'{i}.jsonl').read_bytes() and line.endswith(b'\n')
print('Verified exactly',len(P),'reserved raw lines, newlines, source records, chunk hashes and literal statement hashes.')
