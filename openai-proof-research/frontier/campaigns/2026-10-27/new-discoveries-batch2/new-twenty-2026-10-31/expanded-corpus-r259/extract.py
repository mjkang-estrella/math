import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent; B=L.parent; R=L/'reservation.json'
h=lambda b:hashlib.sha256(b).hexdigest()
assert h(R.read_bytes())==(L/'reservation.sha256').read_text().strip()
ids=json.loads(R.read_text())['ids']; out={}
C=B.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
for p in sorted(C.glob('mathdb-normalized-chunk-*.jsonl')):
 for n,raw in enumerate(p.read_bytes().splitlines(keepends=True),1):
  r=json.loads(raw)
  if r['mathdb_id'] in ids:
   k=str(r['mathdb_id']); (L/f'{k}.raw.jsonl').write_bytes(raw)
   out[k]={'record':r,'chunk':str(p),'line_one_based':n,'chunk_sha256':h(p.read_bytes()),'raw_sha256':h(raw),'statement_sha256':h(r['statement'].encode())}
assert set(out)==set(map(str,ids))
(L/'literal-records.json').write_text(json.dumps(out,indent=2))
for k,v in out.items():print(k,v['record']['title'],'\n',v['record']['statement'],'\nSOURCE',v['record']['source_url'],'\n')
for p in [B/'ledger.json',B.parent/'ledger.json']:
 j=json.loads(p.read_text()); (L/('context-'+p.parent.name+'-ledger.json')).write_bytes(p.read_bytes())
 print('LEDGER',p,'keys',list(j))
