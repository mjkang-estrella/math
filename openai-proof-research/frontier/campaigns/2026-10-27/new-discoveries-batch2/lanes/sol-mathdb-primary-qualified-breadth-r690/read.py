exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("refs={}")[0])
ids=set(j(I/'reserved-ids-r690.json')['ids']);out=[]
for e in j(C/'manifest.json')['files']:
 if not e['path'].startswith('corpus/'):continue
 for n,line in enumerate((C/e['path']).open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   out.append({'chunk':e['path'],'line':n,'record':r})
assert len(out)==50
(P/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for x in out:
 r=x['record'];print('\nID',r['mathdb_id'],'KEYS',list(r) if x==out[0] else '');print(r['statement']);print('SOURCE',r.get('references',r.get('source','')))
