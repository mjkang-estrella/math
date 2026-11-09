import json,hashlib,resource,datetime
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent; base=p.parent.parent
H=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((p/'reservation.json').read_text()); expected=(p/'reservation.sha256').read_text().split()[0];actual=H((p/'reservation.json').read_bytes());assert actual==expected
(p/'reservation-check-before.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),expected=expected,actual=actual,ok=True,ids=r['ids']),indent=2))
(p/'raw').mkdir(exist_ok=True); out={}
for f in sorted((base/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 chunkhash=None
 for n,line in enumerate(f.open('rb'),1):
  # all parsing is bounded local text work, no mathematical search
  d=json.loads(line);i=d.get('id',d.get('mathdb_id'))
  if i is not None and int(i) in r['ids']:
   if chunkhash is None:chunkhash=H(f.read_bytes())
   i=str(i);(p/'raw'/f'{i}.jsonl').write_bytes(line)
   statement=d.get('statement',d.get('content',''))
   out[i]=dict(chunk=str(f),line_1based=n,chunk_sha256=chunkhash,raw_sha256=H(line),statement_sha256=H((statement if isinstance(statement,str) else json.dumps(statement,ensure_ascii=False)).encode()),record=d)
assert set(out)==set(map(str,r['ids'])),out.keys()
(p/'literal-provenance.json').write_text(json.dumps(out,indent=2,ensure_ascii=False))
for i in r['ids']:
 d=out[str(i)]['record']; print(i,json.dumps(d,ensure_ascii=False))
