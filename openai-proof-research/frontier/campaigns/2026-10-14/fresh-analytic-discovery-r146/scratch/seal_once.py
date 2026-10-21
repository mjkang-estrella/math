from pathlib import Path
import os,json,hashlib
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r146')
out=r/'MANIFEST.json'
if out.exists():raise SystemExit('Refusing to reseal an existing manifest')
envelopes={'FINAL.md','MANIFEST.json','REPORT.md'}
entries=[]
for base,dirs,files in os.walk(r,followlinks=False):
 for n in dirs+files:
  if (Path(base)/n).is_symlink():raise SystemExit('symlink rejected')
 for n in files:
  p=Path(base)/n;rel=str(p.relative_to(r))
  if rel in envelopes:continue
  b=p.read_bytes();entries.append(dict(path=rel,size=len(b),sha256=hashlib.sha256(b).hexdigest()))
entries.sort(key=lambda e:e['path'])
out.write_text(json.dumps(dict(schema='r146-exact-payload-v1',outside_envelopes=sorted(envelopes),files=entries),indent=2)+'\n')
print('Sealed once:',len(entries),'payload files; three outside envelopes')
