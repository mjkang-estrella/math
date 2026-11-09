import pathlib,json,hashlib,subprocess,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
o=pathlib.Path(__file__).resolve().parent;c=o.parent;b=c.parent;r=json.loads((o/'reservation.json').read_text()); ids=set(r['ids']);h=lambda x:hashlib.sha256(x).hexdigest(); results={};(o/'raw').mkdir(exist_ok=True)
for p in sorted((b/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes();ch=h(data)
 for n,line in enumerate(data.splitlines(keepends=True),1):
  x=json.loads(line)
  if x['mathdb_id'] not in ids:continue
  i=str(x['mathdb_id']);(o/'raw'/f'{i}.jsonl').write_bytes(line)
  results[i]={'record':x,'provenance':{'chunk':str(p),'one_based_line':n,'chunk_sha256':ch,'raw_sha256':h(line),'statement_utf8_sha256':h(x['statement'].encode())},'review_depth':'literal_statement_read; primary_body_unread','outcome':'HOLD_unresolved','credit':0}
assert len(results)==40
(o/'intake.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
with (o/'statements.txt').open('w') as f:
 for i,x in results.items():
  q=x['record']; f.write(f"\n### {i} {q['title']}\n{q['statement']}\nSOURCE {q['source_url']}\n{q['references']}\n")
print((o/'statements.txt').read_text())
