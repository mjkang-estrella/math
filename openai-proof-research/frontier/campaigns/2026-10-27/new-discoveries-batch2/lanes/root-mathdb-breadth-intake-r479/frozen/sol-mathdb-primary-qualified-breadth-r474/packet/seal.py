import pathlib,json,hashlib
O=pathlib.Path(__file__).resolve().parents[1]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
entries=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in ['manifest.json','final-receipt.json']:
  entries.append({'path':str(p.relative_to(O)),'bytes':p.stat().st_size,'sha256':sha(p)})
(O/'manifest.json').write_text(json.dumps({'excluded_exact_relative_paths':['manifest.json','final-receipt.json'],'files':entries},indent=2)+'\n')
print('sealed files',len(entries))
