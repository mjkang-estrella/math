from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent
corpus=p.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
rows=json.loads((p/'literal-records.json').read_text());res=json.loads((p/'results.json').read_text())
assert len(rows)==len(res)==40
assert {x['id'] for x in rows}==set(json.loads((p/'reservation.json').read_text())['ids'])
cache={}
for x in rows:
 name=x['chunk']
 if name not in cache:
  b=(corpus/name).read_bytes();cache[name]=(hashlib.sha256(b).hexdigest(),b.decode().splitlines())
 sha,lines=cache[name];line=lines[x['line']-1]
 assert sha==x['chunk_sha256']
 assert hashlib.sha256(line.encode()).hexdigest()==x['line_sha256']
 assert json.loads(line)==x['record']
 assert res[str(x['id'])]['line_sha256']==x['line_sha256']
assert sum(r['primary_proof_body_reviewed'] for r in res.values())==4
assert sum(r['accepted_credit'] for r in res.values())==0
for receiptfile in ['source-receipts.json','additional-receipts.json']:
 for r in json.loads((p/receiptfile).read_text()):
  if 'sha256' in r:
   fn=r.get('file',r['name']+'.pdf')
   assert hashlib.sha256((p/fn).read_bytes()).hexdigest()==r['sha256']
r=json.loads((p/'cumulative-receipt.json').read_text());assert hashlib.sha256((p/'cumulative.pdf').read_bytes()).hexdigest()==r['sha256']
for r in json.loads((p/'reused-registry-receipts.json').read_text()):assert r['matches']
print('PASS: all40 exact immutable records, chunk and line hashes, result bindings, all downloaded primary hashes. Primary/body4; literal-only36; credit0. No Lean theorem claimed.')
