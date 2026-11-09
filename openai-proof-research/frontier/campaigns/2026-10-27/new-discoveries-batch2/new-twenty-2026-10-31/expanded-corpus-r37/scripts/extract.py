import resource,os
resource.setrlimit(resource.RLIMIT_CPU,(60,60))
resource.setrlimit(resource.RLIMIT_AS,(1536*1024**2,1536*1024**2))
os.sched_setaffinity(0,{0,1})
import pathlib,json,hashlib,subprocess
B=pathlib.Path('openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'); L=B/'new-twenty-2026-10-31/expanded-corpus-r37'; R=json.loads((L/'reservation.json').read_text()); ids=set(R['ids']);out={}
sha=lambda x:hashlib.sha256(x).hexdigest()
for f in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=f.read_bytes(); ch=sha(data)
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line);i=d['mathdb_id']
  if i in ids:
   (L/f'raw/{i}.jsonl').write_bytes(line)
   out[str(i)]={'record':d,'chunk':str(f),'line_one_based':n,'chunk_sha256':ch,'raw_sha256':sha(line),'statement_sha256':sha(d['statement'].encode())}
(L/'extracted.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
with (L/'statements.txt').open('w') as w:
 for i,x in out.items():
  d=x['record'];w.write(f"\n{i} {d['title']}\n{d['statement']}\nSOURCE {d['source_name']} {d['source_url']}\n")
print(len(out))
