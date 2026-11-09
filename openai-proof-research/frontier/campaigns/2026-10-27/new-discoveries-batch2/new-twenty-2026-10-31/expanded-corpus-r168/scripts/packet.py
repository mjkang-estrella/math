import pathlib,zipfile,hashlib,json
D=pathlib.Path(__file__).resolve().parents[1]
files=['lean/SplitMatching.lean','lean/Audit.lean','lean/README.md','CANDIDATE.md','scripts/limited.py','scripts/lean.sh','scripts/checker.sh','bin/lean']
with zipfile.ZipFile(D/'Lean-packet.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in files:z.write(D/f,f)
 z.writestr('trust.json',json.dumps({'lean':'4.34.1','mathlib_commit':'d13f23b723b8a846827a245b89c10fc7d3f11612','manifest_sha256':hashlib.sha256((D.parents[3]/'2026-10-14/formal/lake-manifest.json').read_bytes()).hexdigest() if (D.parents[3]/'2026-10-14/formal/lake-manifest.json').exists() else 'see lane dependency receipt','allowed_axioms':['propext','Classical.choice','Quot.sound'],'upstream_full_rebuild':False},indent=2))
p=D/'extracted-packet';p.mkdir(exist_ok=False)
with zipfile.ZipFile(D/'Lean-packet.zip') as z:
 for i in z.infolist():
  q=pathlib.PurePosixPath(i.filename)
  assert not q.is_absolute() and '..' not in q.parts
  target=p.joinpath(*q.parts);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(i))
print('extracted',len(files),'source files; no cached oleans')
