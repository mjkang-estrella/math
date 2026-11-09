from pathlib import Path
import zipfile,hashlib,json
root=Path(__file__).resolve().parent.parent
packets=[('r4a','chord-source.zip',54),('r4b','chord-comb4-source.zip',117)]
merged={}; shared=[]
for lane,archive,count in packets:
 with zipfile.ZipFile(root.parent/('chord-formal-'+lane)/archive) as z:
  files={Path(n).name:z.read(n) for n in z.namelist() if n.endswith('.lean')}
  assert len(files)==count,(lane,len(files))
  for n,b in files.items():
   if n in merged:
    assert merged[n]==b,n
    shared.append(n)
   merged[n]=b
assert len(shared)==33 and len(merged)==138
for n,b in merged.items(): (root/'src'/n).write_bytes(b)
pending=set(merged); order=[]
while pending:
 ready=sorted(n for n in pending if all(dep+'.lean' not in pending for line in merged[n].decode().splitlines() if line.startswith('import ') for dep in line[7:].split()))
 assert ready
 order+=ready; pending.difference_update(ready)
(root/'modules.txt').write_text(''.join(n[:-5]+'\n' for n in order))
(root/'frozen'/'manifest.json').write_text(json.dumps({n:hashlib.sha256(b).hexdigest() for n,b in sorted(merged.items())},indent=2)+'\n')
(root/'merge.json').write_text(json.dumps({'modules':len(merged),'shared_byte_identical':len(shared),'conflicts':0},indent=2)+'\n')
print('Merged',len(merged),'modules; shared byte-identical:',len(shared))
