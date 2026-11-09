import pathlib,hashlib,json
L=pathlib.Path(__file__).resolve().parent
exclude={'manifest.json','final-receipt.txt'};out=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and str(p.relative_to(L)) not in exclude:
  b=p.read_bytes();out.append({'path':str(p.relative_to(L)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'manifest.json').write_text(json.dumps({'files':out,'excluded_exact_paths':sorted(exclude)},indent=2)+'\n')
print('sealed',len(out))
