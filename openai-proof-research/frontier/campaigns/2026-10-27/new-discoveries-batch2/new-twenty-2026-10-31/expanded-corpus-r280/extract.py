import pathlib,json,hashlib,resource,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
r=pathlib.Path(__file__).resolve().parent; b=r.parent.parent
sha=lambda x:hashlib.sha256(x).hexdigest()
expected=(r/'reservation.sha256').read_text().split()[0]; actual=sha((r/'reservation.json').read_bytes()); assert expected==actual
(r/'reservation-before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'expected':expected,'actual':actual,'pass':True},indent=2))
ids=json.loads((r/'reservation.json').read_text())['ids']; out={}
for p in sorted((b/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes(); ch=sha(data)
 for n,line in enumerate(data.splitlines(keepends=True),1):
  # Avoid parsing all records
  if not any(str(i).encode() in line for i in ids): continue
  row=json.loads(line); key=row.get('mathdb_id',row.get('id'))
  if key is None: print('KEYS',list(row)); continue
  if int(key) not in ids: continue
  i=str(key); (r/'evidence'/f'{i}.raw.jsonl').write_bytes(line)
  out[i]={'chunk_path':str(p),'line_1based':n,'chunk_sha256':ch,'raw_sha256':sha(line),'raw_newline_preserved':line.endswith(b'\n'),'record':row}
assert len(out)==20, list(out)
(r/'raw-records.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for i in ids:
 print('\nID',i, json.dumps(out[str(i)]['record'],ensure_ascii=False))
