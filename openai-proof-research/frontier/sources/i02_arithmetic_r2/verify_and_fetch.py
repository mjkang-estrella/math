"""Independent source integrity check and primary-literature cache; no shared writes."""
from pathlib import Path
import hashlib, json, urllib.request, subprocess

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
pin = json.loads((ROOT/'sources/upstream.json').read_text())['commit']
tree = {r['path']: r['sha'] for r in json.loads((ROOT/'sources/preprints-tree.json').read_text())['tree'] if r['type']=='blob'}
original = json.loads((ROOT/'frontier/sources/i02_arithmetic/manifest-artin.json').read_text())
rows = []
for r in original['files']:
    p = ROOT/'frontier/sources/i02_arithmetic'/r['local']
    b = p.read_bytes()
    blob = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert blob == tree[r['path']] == r['git_blob_expected']
    rows.append(dict(path=r['path'], local=str(p.relative_to(ROOT)), git_blob=blob, sha256=hashlib.sha256(b).hexdigest(), bytes=len(b)))
qpath = 'preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex'
p = ROOT/'frontier/sources/arithmetic/The-Quasi-Riemann-Hypothesis-September-30-2026__build__paper.tex'
b = p.read_bytes()
blob = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
assert blob == tree[qpath]
rows.append(dict(path=qpath, local=str(p.relative_to(ROOT)), git_blob=blob, sha256=hashlib.sha256(b).hexdigest(), bytes=len(b)))
literature = [
 ('kurlberg_pomerance_2013.pdf','https://msp.org/ant/2013/7-4/ant-v7-n4-p08-p.pdf'),
 ('kurlberg_pomerance_period.pdf','https://math.dartmouth.edu/~carlp/PDF/par11.pdf'),
 ('goldmakher_martin_peringuey_v1.html','https://arxiv.org/html/2502.19601v1'),
 ('kim_1509_03768.html','https://arxiv.org/abs/1509.03768'),
]
external = []
for name,url in literature:
    p = OUT/name
    if not p.exists():
        with urllib.request.urlopen(url, timeout=45) as response:
            p.write_bytes(response.read())
    b = p.read_bytes()
    external.append(dict(local=str(p.relative_to(ROOT)),url=url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
    if p.suffix == '.pdf':
        subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
inputs = []
for name in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/iterations/README.md','frontier/iterations/i02-arithmetic.md','frontier/experiments/i02_arithmetic_index_decomposition_check.py','frontier/experiments/i02_arithmetic_qrh_geometry.py']:
    b=(ROOT/name).read_bytes()
    inputs.append(dict(path=name,sha256=hashlib.sha256(b).hexdigest()))
(OUT/'manifest.json').write_text(json.dumps(dict(pin=pin,upstream=rows,literature=external,review_inputs=inputs),indent=2)+'\n')
print(json.dumps(dict(verified_upstream_files=len(rows),cached_primary_sources=len(external),pin=pin)))
