import pathlib,json,re,urllib.request,hashlib,datetime
r=pathlib.Path(__file__).parent;b=r.parent/'sol-polyomino57-full-final-review-r1/live';rows=[]
for f in b.glob('*.json'):
 if not any(x in f.name for x in ('D5','Problems','tree','preprints')):continue
 try:d=json.loads(f.read_text())
 except:continue
 for t in d.get('tree',[]):
  if re.search('semigroup|pseudo.?frobenius|Chomicz|Kien|Murai',t['path'],re.I):rows.append({'file':str(f),'path':t['path'],'tree':d.get('sha')})
(r/'registry-broad.json').write_text(json.dumps(rows,indent=2))
for x in rows:print(x['file'].split('/')[-1],x['path'])
