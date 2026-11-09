import hashlib,json,shutil,zipfile,stat
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parent
paths=[]
for root in ['slownim-review-r1','slownim-root-check-r1']:
 paths += [p for p in (B/root).rglob('*') if p.is_file()]
for root in ['slownim-formal-r1','slownim-parent-final-r1']:
 paths += [p for p in (B/root).rglob('*') if p.is_file() and not any(s in p.parts for s in ['build','.lake','cache','tmp']) and p.suffix not in ['.olean','.ilean','.c','.o']]
E=B/'expanded-corpus-r204'
for name in ['CANDIDATE-360653-361128.md','SUMMARY.md','results.json','raw/360653.jsonl','raw/361128.jsonl']:
 paths.append(E/name)
for root in ['scripts','outputs/nim']:
 paths += [p for p in (E/root).rglob('*') if p.is_file()]
for arxiv in ['2311.03257','2312.08382','2304.06498','2311.13511']:
 paths += [p for p in (E/'sources/tex'/arxiv).rglob('*') if p.is_file()]
for name in ['cr-gmrule.json','cr-screw.json','abs-2311.03257.html','abs-2312.08382.html','abs-2304.06498.html','src-2311.03257.bin','src-2312.08382.bin','src-2304.06498.bin']:
 paths.append(E/'sources'/name)
paths += [B/'slownim-root-ruling-r1.json',B/'AGENTS.md',B.parent/'AGENTS.md',B.parents[4]/'AGENTS.md']
paths=sorted(set(p.resolve() for p in paths))
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest={str(p):digest(p) for p in paths}
(L/'inputs.before.json').write_text(json.dumps(manifest,indent=2)+'\n')
for p in paths:
 try:rel=p.relative_to(B)
 except ValueError:rel=Path('governing')/p.parent.name/p.name
 target=L/'evidence'/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,target)
packet=L/'source.zip';shutil.copyfile(B/'slownim-formal-r1/source.zip',packet)
assert digest(packet)=='e1f35146078b39a2ace25101b02806404f741adb7042e1376f77d7c09e359996'
dest=L/'safe-extracted-packet';dest.mkdir(exist_ok=True)
members=[]
with zipfile.ZipFile(packet) as z:
 assert sum(i.file_size for i in z.infolist())<20*1024**2
 for i in z.infolist():
  p=Path(i.filename);assert not p.is_absolute() and '..' not in p.parts
  assert not stat.S_ISLNK(i.external_attr>>16)
  target=(dest/p).resolve();assert target.is_relative_to(dest)
  if i.is_dir():target.mkdir(parents=True,exist_ok=True)
  else:
   target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(i))
   members.append(dict(path=i.filename,sha256=digest(target),bytes=i.file_size))
(L/'safe-extraction.json').write_text(json.dumps(dict(status='PASS',packet_sha256=digest(packet),members=members,executed=False),indent=2)+'\n')
shutil.copyfile(B/'slownim-review-r1/scripts/check.py',L/'recompute.py')
print('Frozen copies and safe extraction complete; no packet code executed.')
