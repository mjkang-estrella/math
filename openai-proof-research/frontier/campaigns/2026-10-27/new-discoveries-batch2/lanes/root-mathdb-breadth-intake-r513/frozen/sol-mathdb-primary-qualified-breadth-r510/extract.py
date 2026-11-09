import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r509';C=L/'pi-mathdb-full-corpus-inventory-r301'
J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest()
ids=set(J(I/'reserved-ids.json')['ids']);rows=[]
for e in J(C/'manifest.json')['files']:
 if not e['path'].startswith('corpus/'):continue
 p=C/e['path']
 for n,l in enumerate(p.open(),1):
  r=json.loads(l)
  if r['mathdb_id'] in ids:rows.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'corpus_line':n,'statement':r['statement'],'statement_utf8_sha256':H(r['statement'].encode()),'canonical_record_sha256':H(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'record':r})
assert len(rows)==50
(P/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for a in rows:print('\nID',a['mathdb_id'],json.dumps(a['record'],ensure_ascii=False))
