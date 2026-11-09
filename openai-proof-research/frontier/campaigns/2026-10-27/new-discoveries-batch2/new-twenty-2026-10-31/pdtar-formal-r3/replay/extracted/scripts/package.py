import pathlib, hashlib, json, zipfile
D=pathlib.Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=sorted(list((D/'PDTAR').glob('*.lean'))+list((D/'scripts').glob('*.py'))+list((D/'scripts').glob('*.lean'))+[D/'module-order.json'])
pins=json.loads((D/'inputs/r2a/manifest.json').read_text())['pins']
m=dict(modules=json.loads((D/'module-order.json').read_text()),files={str(p.relative_to(D)):sha(p) for p in files},pins=pins,mathlib_revision='d13f23b723b8a846827a245b89c10fc7d3f11612')
(D/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
with zipfile.ZipFile(D/'pdtar-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files+[D/'manifest.json']:z.write(p,str(p.relative_to(D)))
print(sha(D/'pdtar-source.zip'))
