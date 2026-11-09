import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parent; B=D.parent.parent; R=json.loads((D/'reservation.json').read_bytes()); H=lambda b:hashlib.sha256(b).hexdigest()
(D/'raw').mkdir(exist_ok=True); receipts=[]; old={}
for p,h in R['prior_report_hashes'].items():
 b=pathlib.Path(p).read_bytes(); assert H(b)==h; receipts.append(dict(path=p,sha256=h,verified=True))
 for row in json.loads(b):
  if row['mathdb_id'] in R['ids']: old[str(row['mathdb_id'])]=row
assert len(old)==40
records={};chunks={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes()
 for i,line in enumerate(data.splitlines(keepends=True),1):
  row=json.loads(line); id=str(row.get('mathdb_id'))
  if id in old:
   assert id not in records
   (D/'raw'/f'{id}.jsonl').write_bytes(line); records[id]=row; chunks[id]=dict(path=str(p),line_one_based=i,raw_line_sha256=H(line),chunk_sha256=H(data),statement_sha256=H(row['statement'].encode()),newline_preserved=line.endswith(b'\n'))
assert len(records)==40
(D/'old-dispositions.json').write_text(json.dumps(old,indent=2));(D/'records.json').write_text(json.dumps(records,indent=2));(D/'raw-bindings.json').write_text(json.dumps(chunks,indent=2));(D/'binding-receipt.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prior_reports=receipts,records=40),indent=2))
for id,x in records.items(): assert x['statement']==old[id]['statement'],id
print('40 exact records; all three immutable reports match; exact statements match; raw lines retained')
