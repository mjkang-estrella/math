import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent; C=L.parent; B=C.parent
ids=json.loads((L/'reservation.json').read_text())['ids']; out={}
h=lambda b:hashlib.sha256(b).hexdigest()
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for n,b in enumerate(p.read_bytes().splitlines(keepends=True),1):
  d=json.loads(b)
  if d.get('mathdb_id') in ids:
   i=str(d['mathdb_id']); (L/(i+'.raw.jsonl')).write_bytes(b)
   out[i]={'record':d,'provenance':{'chunk':str(p),'one_based_line':n,'chunk_sha256':h(p.read_bytes()),'raw_sha256':h(b),'statement_sha256':h(d['statement'].encode()),'raw_newline_preserved':b.endswith(b'\n')}}
(L/'literal-records.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for i,v in out.items(): print(i,v['record']['title'],'\n',v['record']['statement'],'\n')
# Read complete ledgers, retain narrow matching/protected history for review.
for p in [C/'ledger.json',B/'ledger.json',B/'prior-campaign-context.json']:
 d=p.read_text(); (L/(p.parent.name+'-'+p.name)).write_text(d)
print('ledger bytes',sum(p.stat().st_size for p in L.glob('*ledger.json')))
