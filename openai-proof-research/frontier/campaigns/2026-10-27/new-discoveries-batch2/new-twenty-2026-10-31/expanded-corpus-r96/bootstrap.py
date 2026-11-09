import pathlib,json,hashlib,datetime,urllib.request,resource,os
L=pathlib.Path(__file__).resolve().parent; os.chdir(L)
for d in ['scripts','raw','sources','outputs','logs']: (L/d).mkdir(exist_ok=True)
h=lambda b:hashlib.sha256(b).hexdigest()
ids=set(json.loads((L/'reservation.json').read_text())['ids']); rows={}
C=L.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
for p in sorted(C.glob('*.jsonl')):
 b=p.read_bytes(); ch=h(b)
 for i,line in enumerate(b.splitlines(keepends=True),1):
  r=json.loads(line); k=r.get('mathdb_id',r.get('id'))
  try:k=int(k)
  except:continue
  if k in ids:
   (L/f'raw/{k}.jsonl').write_bytes(line); rows[str(k)]={'row':r,'chunk':str(p),'line':i,'chunk_sha256':ch,'raw_sha256':h(line)}
(L/'extracted.json').write_text(json.dumps(rows,indent=2))
print('extracted',len(rows))
for k,v in rows.items():print(k,json.dumps(v['row'],ensure_ascii=False))
