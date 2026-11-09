exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("bind(I/'manifest.json')")[0])
ids=set(j(I/'reserved-ids-r706.json')['ids']);out=[]
for e in j(C/'manifest.json')['files']:
 if not e['path'].startswith('corpus/'):continue
 for n,line in enumerate((C/e['path']).open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:out.append({'mathdb_id':r['mathdb_id'],'chunk':e['path'],'line':n,'record':r,'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'statement_sha256':h(r['statement'].encode())})
assert len(out)==50
(P/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for x in out:
 print('\nID',x['mathdb_id'],json.dumps(x['record'],ensure_ascii=False))
