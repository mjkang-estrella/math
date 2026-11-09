exec((__import__('pathlib').Path(__file__).resolve().parent/'bind.py').read_text())
ids=set(res['ids']);out=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:out.append({'mathdb_id':r['mathdb_id'],'chunk':str(p),'line':n,'statement':r['statement'],'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(out)==50
out.sort(key=lambda r:res['ids'].index(r['mathdb_id']))
(P/'assigned-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
(P/'reading.txt').write_text('\n\n'.join(str(r['mathdb_id'])+' '+r['record'].get('title','')+'\n'+r['statement']+'\nSOURCES '+json.dumps({k:v for k,v in r['record'].items() if 'source' in k or 'reference' in k},ensure_ascii=False) for r in out))
print((P/'reading.txt').read_text())
