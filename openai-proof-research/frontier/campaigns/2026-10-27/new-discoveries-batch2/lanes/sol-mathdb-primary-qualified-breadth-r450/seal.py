import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(L)),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
(L/'manifest.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':files,'excluded':['manifest.json','final-receipt.json']},indent=2)+'\n')
print('sealed',len(files),'payload files')
