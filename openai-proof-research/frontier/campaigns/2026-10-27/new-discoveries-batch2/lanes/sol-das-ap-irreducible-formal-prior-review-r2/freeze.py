import pathlib,hashlib,json,shutil,tarfile
B=pathlib.Path(__file__).resolve().parent; batch=B.parent.parent
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
def freeze(p, dest):
 a=h(p); dest.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(p,dest)
 assert a==h(p)==h(dest)
 rows.append(dict(original=str(p),copy=str(dest),sha256=a))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 freeze(batch/name,B/'administrative'/name)
src=B.parent/'sol-das-ap-irreducible-source-formal-r1'
freeze(src/'source-only.tar.gz',B/'frozen/source-only.tar.gz')
assert h(B/'frozen/source-only.tar.gz')=='a8e63b8b21d9963e64ce8a9e6dc6cda4789228b418e351417aa5b3a20259f0d3'
for name in ['review.md','freeze.json','coverage.json']:
 freeze(B.parent/'sol-das-ap-irreducible-preliminary-review-r1'/name,B/'prior'/name)
with tarfile.open(B/'frozen/source-only.tar.gz') as t:
 for m in t.getmembers():
  assert m.isfile() or m.isdir()
  assert not pathlib.PurePosixPath(m.name).is_absolute() and '..' not in pathlib.PurePosixPath(m.name).parts
 t.extractall(B/'extracted',filter='data')
 (B/'archive-members.json').write_text(json.dumps([dict(name=m.name,size=m.size,mtime=m.mtime,uid=m.uid,gid=m.gid,mode=m.mode) for m in t.getmembers()],indent=2))
for p in sorted((B/'extracted').rglob('*')):
 if p.is_file(): rows.append(dict(copy=str(p),sha256=h(p)))
(B/'freeze.json').write_text(json.dumps(rows,indent=2))
print(json.dumps(rows,indent=2))
