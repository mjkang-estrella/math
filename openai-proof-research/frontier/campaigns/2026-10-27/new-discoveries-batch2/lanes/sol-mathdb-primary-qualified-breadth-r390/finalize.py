import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent;out=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ('manifest.json','final-receipt.json'):
  b=p.read_bytes();out.append(dict(path=str(p.relative_to(L)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(L/'manifest.json').write_text(json.dumps({'files':out,'exclusions':['manifest.json','final-receipt.json']},indent=2)+'\n')
