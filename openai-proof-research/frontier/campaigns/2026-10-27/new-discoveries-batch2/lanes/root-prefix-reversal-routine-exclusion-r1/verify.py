from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-prefix-reversal-row-preliminary-review-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
m=json.loads((S/'manifest.json').read_text())
for r in m['files']:
 p=S/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
assert {r['path'] for r in m['files']}=={str(p.relative_to(S)) for p in S.rglob('*') if p.is_file() and p.name not in ['manifest.json','verified-manifest.json']}
b=json.loads((S/'before.json').read_text());assert len(b['files'])==84
for r in b['files']:
 for p in [Path(r['path']),S/r['copy']]:assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256']
assert sha(P.parent/'root-r169-preliminary-freeze-r1/review-freeze.json')==b['freeze_sha256']
code=(S/'check.py').read_text().split('# Independent orbit control:',1)[1].split('# Compact source access',1)[0]
code=code.split('\n',1)[1]
script='import json,math,datetime\nfrom pathlib import Path\nL=Path(__file__).resolve().parent\nresults=[]\n'+code
(P/'independent-replay.py').write_text(script)
with (P/'independent-replay.log').open('w') as f:subprocess.run([sys.executable,str(P/'independent-replay.py')],check=True,stdout=f,stderr=subprocess.STDOUT)
a=json.loads((P/'independent-checks.json').read_text());expected=json.loads((S/'independent-checks.json').read_text())
for k in ['independent_orbits','boundary_a_kplus1','tree_block_controls','scope']:assert a[k]==expected[k]
files=[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':files},indent=2)+'\n')
out={'status':'PASS','originals':84,'manifest':len(m['files']),'review_files':len(files),'orbit_controls':a['independent_orbits'],'boundary_controls':a['boundary_a_kplus1'],'tree_controls':a['tree_block_controls'],'credit':0}
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
