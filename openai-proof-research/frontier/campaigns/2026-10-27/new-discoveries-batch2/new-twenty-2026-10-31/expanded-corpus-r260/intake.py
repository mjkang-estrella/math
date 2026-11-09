import pathlib,json,hashlib,datetime,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent; B=L.parent; R=B.parent
h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((L/'reservation.json').read_text());before=h((L/'reservation.json').read_bytes());assert before==(L/'reservation.sha256').read_text().strip();(L/'reservation-before.json').write_text(json.dumps({'sha256':before,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}))
ids=set(r['ids']);records={}
for f in sorted((R/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for n,raw in enumerate(f.open('rb'),1):
  o=json.loads(raw);i=o.get('mathdb_id',o.get('id'))
  if i in ids:
   (L/f'{i}.raw.jsonl').write_bytes(raw);records[str(i)]={'record':o,'chunk':str(f),'line_one_based':n,'raw_sha256':h(raw),'chunk_sha256':h(f.read_bytes())}
assert len(records)==20
(L/'literal-records.json').write_text(json.dumps(records,indent=2))
for i,x in records.items():
 print(i,json.dumps(x['record'],ensure_ascii=False))
