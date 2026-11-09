exec(open(__file__.replace('read_records.py','bind.py')).read().split('b={}')[0])
ids=set(j(I/'reserved-ids.json')['ids']);out=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   s=r['statement'];out.append({'mathdb_id':r['mathdb_id'],'chunk':str(p),'line':n,'statement':s,'statement_utf8_sha256':hashlib.sha256(s.encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(out)==50
(P/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for x in out:print('\nID',x['mathdb_id'],json.dumps(x['record'],ensure_ascii=False))
