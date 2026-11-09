import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-receipt.json']:
  b=p.read_bytes();files.append(dict(path=p.relative_to(L).as_posix(),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
(L/'manifest.json').write_text(json.dumps(dict(schema=1,scope='exact lane payload; manifest and separate receipt excluded from self-hashing',files=files),indent=2)+'\n')
# Receipt placeholder permits exact-membership validation before it is replaced.
(L/'final-receipt.json').write_text('{}\n')
print('sealed',len(files),'files')
