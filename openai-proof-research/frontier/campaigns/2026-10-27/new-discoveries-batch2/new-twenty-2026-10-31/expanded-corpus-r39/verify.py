from pathlib import Path
import json,hashlib,resource,os
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
w=Path(__file__).resolve().parent;h=lambda x:hashlib.sha256(x).hexdigest();r=json.loads((w/'reservation.json').read_text());ex=json.loads((w/'extraction.json').read_text());res=json.loads((w/'results.json').read_text());assert len(res)==40 and set(res)==set(map(str,r['ids']))
for i,e in ex.items():
 p=Path(e['chunk']);raw=p.read_bytes();assert h(raw)==e['chunk_sha256'];line=raw.splitlines(keepends=True)[e['line_1based']-1];assert line==(w/'raw'/f'{i}.jsonl').read_bytes() and line.endswith(b'\n');assert h(line)==e['raw_sha256'];d=json.loads(line);assert h(d['statement'].encode())==e['statement_sha256'];assert res[i]['literal_statement']==d['statement'];assert res[i]['credit_proposed']==0
for p in [w/'sources/receipts.json',w/'sources/more-receipts.json']:
 for e in json.loads(p.read_text()):
  if 'sha256' not in e:continue
  name=e['url'].rsplit('/',1)[-1]
  matches=[x for x in (w/'sources').iterdir() if x.is_file() and h(x.read_bytes())==e['sha256']];assert matches,e['url']
manifest={str(p.relative_to(w)):h(p.read_bytes()) for p in sorted(w.rglob('*')) if p.is_file() and p.name not in ['artifact-sha256.json','verify.log']};(w/'artifact-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n');print('PASS: exactly40 IDs; all raw newline bytes, chunk/statement/source receipt hashes; zero proposed credit. Artifact manifest generated.')
