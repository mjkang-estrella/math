from pathlib import Path,PurePosixPath
import hashlib,json,zipfile,stat,shutil,re
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
z=L.parent/'coxeter-normal-form-r3/330264-r3-FULL-LEAN.zip'
assert sha(z.read_bytes())=='2cab69a4914f29fb3f934b8f57c8807bcb3298bea7e1b535246e9e205e3acaab'
O=L/'original';O.mkdir()
with zipfile.ZipFile(z) as a:
 for i in a.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
  assert not i.filename.endswith(('.olean','.ilean','.so'))
  if i.is_dir():continue
  d=O/p;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(a.read(i))
m=json.loads((O/'packet-manifest.json').read_text())
rows={}
for f,h in m['files'].items():
 b=(O/f).read_bytes();assert sha(b)==h;rows[f]=h
(L/'input-verification.json').write_text(json.dumps({'archive':sha(z.read_bytes()),'manifest_files':rows},indent=2))
S=L/'source';S.mkdir()
for f in O.glob('*.lean'):shutil.copyfile(f,S/f.name)
# One identity per module; data in independent paired modules.
text=(O/'SpectralWitness.lean').read_text()
lines=text.splitlines(keepends=True)
# exact chunks, all declarations preserved verbatim including interstitial comments
bounds=[(8,46,'SpectralAData'),(46,87,'SpectralAPQ'),(87,128,'SpectralAQP'),(128,169,'SpectralAIntertwine'),(169,171,'SpectralAResult'),(171,209,'SpectralCData'),(209,250,'SpectralCPQ'),(250,291,'SpectralCQP'),(291,332,'SpectralCIntertwine'),(332,334,'SpectralCResult'),(334,370,'SpectralLData'),(370,409,'SpectralLPQ'),(409,448,'SpectralLQP'),(448,487,'SpectralLIntertwine'),(487,591,'SpectralTrees'),(591,610,'SpectralIntrinsicG'),(610,629,'SpectralIntrinsicH'),(629,640,'SpectralWitness')]
prev='SpectralDefinitions'
for start,end,name in bounds:
 header=f'import {prev}\nimport Mathlib.Combinatorics.SimpleGraph.Acyclic\nimport Mathlib.Combinatorics.SimpleGraph.LineGraph\nimport Mathlib.Tactic.FinCases\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace ActualSpectra330264\n'
 (S/(name+'.lean')).write_text(header+''.join(lines[start-1:end-1])+'end ActualSpectra330264\n')
 prev=name
mods='GroupSemantics NormalForm TraceAction AutomatonSemantics WordCounting MachineInvariant SpectralDefinitions ConcreteMachine'.split()+[x[2] for x in bounds]+['Endpoint']
(L/'modules.txt').write_text('\n'.join(mods)+'\n')
(L/'split-map.json').write_text(json.dumps(bounds,indent=2))
