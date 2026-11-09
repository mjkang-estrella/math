from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent; B=P.parent.parent; R=json.loads((P/'reservation.json').read_text()); sha=lambda b:hashlib.sha256(b).hexdigest(); receipts=[]
for group in ['prior_report_hashes','input_hashes']:
 for p,h in R[group].items():
  q=Path(p); actual=sha(q.read_bytes()); receipts.append(dict(group=group,path=p,expected=h,actual=actual,match=actual==h)); assert actual==h,(p,actual)
C=B/'lanes/pi-mathdb-full-corpus-inventory-r301'; manifest=json.loads((C/'manifest.json').read_text()); old={}
for p in R['prior_report_hashes']:
 for row in json.loads(Path(p).read_text()):
  if row['mathdb_id'] in R['ids']:old[str(row['mathdb_id'])]=row
(P/'raw').mkdir(exist_ok=True); records={}
for f in manifest['files']:
 if not f['path'].startswith('corpus/'):continue
 q=C/f['path'];raw=q.read_bytes();assert sha(raw)==f['sha256'];receipts.append(dict(path=str(q),sha256=sha(raw),bytes=len(raw),match=True))
 for line,b in enumerate(raw.splitlines(keepends=True),1):
  d=json.loads(b);i=str(d.get('id',d.get('mathdb_id')))
  if i in old:
   (P/'raw'/f'{i}.jsonl').write_bytes(b); records[i]=dict(record=d,path=str(q),line_one_based=line,raw_line_sha256=sha(b),chunk_sha256=sha(raw),literal_statement=old[i]['literal_statement'],literal_sha256=sha(old[i]['literal_statement'].encode()))
   assert old[i].get('statement_sha256',old[i].get('literal_sha256'))==records[i]['literal_sha256']
assert len(records)==40
(P/'input-verification.json').write_text(json.dumps(receipts,indent=2)+'\n');(P/'records.json').write_text(json.dumps(records,indent=2)+'\n');(P/'inherited-dispositions.json').write_text(json.dumps(old,indent=2)+'\n');print('PASS: immutable bindings, 20 chunk hashes, 40 exact raw records and literal hashes')
