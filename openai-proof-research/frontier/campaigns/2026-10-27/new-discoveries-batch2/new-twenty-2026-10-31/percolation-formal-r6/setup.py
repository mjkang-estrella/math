import pathlib,zipfile,hashlib,json
r=pathlib.Path(__file__).resolve().parent
z=zipfile.ZipFile(r/'inherited.zip')
for n in z.namelist():
 p=pathlib.PurePosixPath(n)
 assert not p.is_absolute() and '..' not in p.parts
z.extractall(r/'inherited')
rows=[]
for n in z.namelist():
 p=r/'inherited'/n
 if p.is_file():
  assert p.read_bytes()==z.read(n)
  rows.append({'path':n,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(r/'inherited-source-comparison.json').write_text(json.dumps(rows,indent=2))
for n in ['normalized.cnf','normalized-trimmed.json']:
 p=r.parent/'percolation-formal-r3'/n
 (r/n).write_bytes(p.read_bytes())
 assert hashlib.sha256((r/n).read_bytes()).digest()==hashlib.sha256(p.read_bytes()).digest()
(r/'certificate-sha256.txt').write_text('\n'.join(hashlib.sha256((r/n).read_bytes()).hexdigest()+'  '+n for n in ['normalized.cnf','normalized-trimmed.json'])+'\n')
