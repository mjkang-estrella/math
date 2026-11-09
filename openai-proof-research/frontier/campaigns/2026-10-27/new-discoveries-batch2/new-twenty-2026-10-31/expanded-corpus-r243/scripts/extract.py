import json, pathlib,hashlib
L=pathlib.Path(__file__).resolve().parents[1]; C=L.parent; B=C.parent
ids=set(json.loads((L/'reservation.json').read_text())['ids']); out={}
def h(b):return hashlib.sha256(b).hexdigest()
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 ch=None
 with p.open('rb') as f:
  for i,line in enumerate(f,1):
   r=json.loads(line); k=r.get('mathdb_id',r.get('id'))
   if k in ids:
    if ch is None:ch=h(p.read_bytes())
    (L/f'raw/{k}.jsonl').write_bytes(line)
    out[str(k)]={'chunk':str(p),'line':i,'chunk_sha256':ch,'raw_sha256':h(line),'record':r}
assert len(out)==20,len(out)
(L/'evidence/exact-records.json').write_text(json.dumps(out,indent=2))
for k,v in out.items():print(k,json.dumps(v['record'],ensure_ascii=False))
ledger=json.loads((C/'ledger.json').read_text()); (L/'evidence/ledger-screen.json').write_text(json.dumps({'path':str(C/'ledger.json'),'sha256':h((C/'ledger.json').read_bytes()),'accepted':ledger.get('accepted',[]),'excluded':ledger.get('excluded',{})},indent=2))
