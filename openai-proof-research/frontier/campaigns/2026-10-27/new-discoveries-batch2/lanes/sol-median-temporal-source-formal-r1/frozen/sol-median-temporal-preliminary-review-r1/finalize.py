from pathlib import Path
import json,hashlib,shutil,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((L/'freeze.json').read_text())
for r in records:assert h(Path(r['original']))==h(L/r['copy'])==r['before']==r['after']
candidate=L.parent/'sol-median-dynamics-breadth-depth-r1'
manifest=json.loads((L/'frozen/manifest.json').read_text())
verified=[]
for name,digest in manifest.items():
 if name.startswith('administrative/'):
  target=L/'candidate-administrative'/Path(name).name;target.parent.mkdir(exist_ok=True)
  shutil.copyfile(candidate/name,target)
 else:target=L/'frozen'/name
 assert h(target)==digest,name
 verified.append(name)
(L/'candidate-manifest-audit.json').write_text(json.dumps(dict(passed=True,entries=len(verified),administrative='snapshot hashes only; no live administrative stability assertions',manifest_excludes_itself_and_receipt='manifest.json' not in manifest and 'verification-receipt.json' not in manifest),indent=2))
body=['# Source before/after hashes','', 'All frozen scientific originals and copies matched before reading and at finalization. Administrative snapshots have no immutability claim.','']
for name in ['1911.08613v2.pdf','1207.0893v1.pdf','1902.03349v2.pdf','1912.06524v2.pdf']:
 p=L/'frozen/frozen'/name;body.append(f'- `{name}`: `{h(p)}` (before = copy = after).')
(L/'SOURCE-HASHES.md').write_text('\n'.join(body)+'\n')
out={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.relative_to(L).as_posix() not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(out,indent=2))
print('Final manifest written:',len(out),'entries; candidate manifest checked:',len(verified))
