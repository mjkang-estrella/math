import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r567'
ids=set(json.loads((I/'reserved-ids.json').read_text())['ids']); out=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for line,s in enumerate(p.open(),1):
  r=json.loads(s)
  if r['mathdb_id'] in ids:
   out.append({'mathdb_id':r['mathdb_id'],'chunk':str(p.resolve()),'line':line,'record':r,'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
(D/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for e in out:
 r=e['record'];print('\nID',r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_url'])
