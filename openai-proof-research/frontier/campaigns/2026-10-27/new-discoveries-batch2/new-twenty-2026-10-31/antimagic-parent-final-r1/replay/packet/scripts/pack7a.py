import hashlib,pathlib,zipfile
r=pathlib.Path.cwd()
with zipfile.ZipFile(r.parent/'antimagic-formal-r4b/source.zip') as z:
 for name in z.namelist():
  if name.endswith('.lean') and (r/name).exists() and name not in ('Antimagic4BAudit.lean',):
   assert (r/name).read_bytes()==z.read(name),name
with zipfile.ZipFile(r.parent/'antimagic-formal-r6a/source.zip') as z:
 names=[s for s in z.namelist() if s.endswith('.lean')]
 assert len(names)==45
 for name in names: assert (r/name).read_bytes()==z.read(name),name
paths=list(r.glob('*.lean'))
paths += [r/p for p in ['SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','NEXT-ROUND.md','results.json','inherited-before.sha256','inherited-after.sha256','bridge-before.sha256','bridge-imports.sha256']]
paths += [r/'scripts'/p for p in ['capped.sh','env.sh','bin/lean','check7a.sh','build-base.sh','replay7a.sh','regression.py','review-verify.py','grid5a.py','grid6a.py','grid7a.py','report7a.py','pack7a.py']]
with zipfile.ZipFile(r/'source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(paths):
  n=p.relative_to(r)
  assert not n.is_absolute() and '..' not in n.parts
  z.write(p,str(n))
print('source.zip',hashlib.sha256((r/'source.zip').read_bytes()).hexdigest(),len(paths),'safe source files')
