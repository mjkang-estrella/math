exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split('for lane in')[0])
a=json.loads((L/'root-mathdb-breadth-intake-r433/reserved-ids.json').read_text()); ids=set(a['ids']);rows=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   rows.append({'record':r,'original':str(p),'line':n,'literal_statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50
(O/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for x in rows:
 r=x['record'];print('\nID',r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE:',r['source_url'],'\nREFERENCES:',r.get('references'),'\nSOLUTIONS:',r.get('solutions'))
