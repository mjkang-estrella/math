import pathlib,runpy,sys,json,hashlib,datetime,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent;C=L.parent;B=C.parent
h=lambda b:hashlib.sha256(b).hexdigest()
sys.argv=['reserve8.py',str(C)]
g=runpy.run_path(str(C/'root-intake-r60/reserve8.py'),run_name='__main__');r=g['RESULT']
(L/'reservation.json').write_text(json.dumps(r,indent=2))
ids=set(r['ids']);out={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 raw=p.read_bytes()
 for n,line in enumerate(raw.splitlines(keepends=True),1):
  d=json.loads(line)
  if d.get('mathdb_id') in ids:
   i=d['mathdb_id'];(L/f'{i}.raw.jsonl').write_bytes(line)
   out[str(i)]={'record':d,'provenance':{'chunk':str(p),'line_one_based':n,'chunk_sha256':h(raw),'raw_sha256':h(line),'statement_sha256':h(d['statement'].encode()),'raw_includes_newline':line.endswith(b'\n')}}
(L/'literal-records.json').write_text(json.dumps(out,indent=2,ensure_ascii=False))
for i,x in out.items():print(i,x['record']['title'],'\n',x['record']['statement'],'\nSOURCE',x['record'].get('source_url'))
for p in [B/'ledger.json',C/'ledger.json',C/'STATUS.md',B/'prior-campaign-context.json',pathlib.Path('openai-proof-research/sources/CONTENTS.md')]:
 (L/('context-'+p.parent.name+'-'+p.name)).write_bytes(p.read_bytes())
