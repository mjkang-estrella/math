import pathlib,json,hashlib,resource,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent; C=L.parent; B=C.parent
h=lambda b:hashlib.sha256(b).hexdigest()
ids=set(json.loads((L/'reservation.json').read_text())['ids']);out={}
(L/'records').mkdir(exist_ok=True)
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 b=p.read_bytes()
 for n,line in enumerate(b.splitlines(keepends=True),1):
  d=json.loads(line)
  if d.get('mathdb_id') in ids:
   i=d['mathdb_id'];(L/'records'/f'{i}.jsonl').write_bytes(line)
   out[str(i)]={'record':d,'provenance':{'chunk':str(p),'line_1based':n,'chunk_sha256':h(b),'raw_sha256_including_newline':h(line),'statement_utf8_sha256':h(d.get('statement','').encode()),'raw_has_trailing_newline':line.endswith(b'\n')}}
assert len(out)==20
(L/'literal-records.json').write_text(json.dumps(out,indent=2,ensure_ascii=False))
ctx={}
for p in [C/'ledger.json',C/'STATUS.md',B/'ledger.json',B/'prior-campaign-context.json',C/'root-intake-r60/reserve8.py',C/'root-intake-r60/reserve2.py']:
 b=p.read_bytes();ctx[str(p)]={'sha256':h(b),'content':b.decode()}
(L/'context.json').write_text(json.dumps(ctx,indent=2))
for i,x in out.items():
 d=x['record'];print(i,d['title'],'\n',d['statement'],'\nSOURCE',d.get('source_url'))
