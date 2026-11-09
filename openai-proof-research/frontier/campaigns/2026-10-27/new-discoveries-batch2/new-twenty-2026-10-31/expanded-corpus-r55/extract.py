import json,pathlib,hashlib,resource,os,subprocess
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
out=pathlib.Path(__file__).resolve().parent;b=out.parent.parent;c=b/'lanes/pi-mathdb-full-corpus-inventory-r301';r=json.loads((out/'reservation.json').read_text());ids=set(r['ids']);sha=lambda x:hashlib.sha256(x).hexdigest();records={}
(out/'raw').mkdir(exist_ok=True)
manifest=json.loads((c/'manifest.json').read_text());expected={x['path']:x['sha256'] for x in manifest['files']}
for p in sorted((c/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes();h=sha(data);assert h==expected[str(p.relative_to(c))]
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line)
  if d['mathdb_id'] in ids:
   i=d['mathdb_id'];(out/'raw'/f'{i}.jsonl').write_bytes(line);records[str(i)]={'record':d,'chunk':str(p),'one_based_line':n,'chunk_sha256':h,'raw_line_sha256':sha(line),'statement_utf8_sha256':sha(d['statement'].encode())}
assert len(records)==40
(out/'extracted.json').write_text(json.dumps(records,indent=2,ensure_ascii=False)+'\n')
with (out/'statements.txt').open('w') as f:
 for i,x in records.items():
  d=x['record'];f.write(f"\n{i} {d['title']}\n{d['statement']}\nSOURCE: {d['source_name']} | {d['source_url']}\n")
print((out/'statements.txt').read_text())
