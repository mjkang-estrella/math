import pathlib,json,hashlib,datetime,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,)*2);resource.setrlimit(resource.RLIMIT_CPU,(90,90))
w=pathlib.Path(__file__).resolve().parent;b=w.parent.parent;i=b/'lanes/pi-mathdb-full-corpus-inventory-r301';r=json.loads((w/'reservation.json').read_text());h=lambda x:hashlib.sha256(x).hexdigest()
checks=[]
for p,expected in r['input_hashes'].items():
 actual=h(pathlib.Path(p).read_bytes());checks.append(dict(path=p,expected=expected,actual=actual,match=actual==expected))
(w/'input-verification.json').write_text(json.dumps(checks,indent=2));assert all(c['match'] for c in checks)
(w/'raw').mkdir(exist_ok=True);out={}; manifest=json.loads((i/'manifest.json').read_text())
for ent in manifest['files']:
 if not ent['path'].startswith('corpus/'):continue
 p=i/ent['path'];data=p.read_bytes();assert h(data)==ent['sha256']
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line)
  if d['mathdb_id'] not in r['ids']:continue
  id=str(d['mathdb_id']);(w/'raw'/f'{id}.jsonl').write_bytes(line)
  out[id]=dict(record=d,chunk=str(p),line_one_based=n,chunk_sha256=h(data),raw_sha256=h(line),statement_sha256=h(d['statement'].encode()))
assert len(out)==40
(w/'records.json').write_text(json.dumps(out,indent=2,ensure_ascii=False))
(w/'statements.txt').write_text('\n\n'.join(f"{k} {v['record']['title']}\n{v['record']['statement']}\nSOURCE {v['record']['source_url']}" for k,v in out.items()))
print((w/'statements.txt').read_text())
