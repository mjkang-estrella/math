import pathlib,json,hashlib
W=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(W.rglob('*')):
 if p.is_file() and p.name not in [] and str(p.relative_to(W)) not in {'manifest.json','final-receipt.jsonl'}:
  b=p.read_bytes();files.append({'path':str(p.relative_to(W)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(W/'manifest.json').write_text(json.dumps({'files':files,'excluded_filenames':['manifest.json','final-receipt.jsonl']},indent=2)+'\n');print('sealed',len(files),'payload files')
