import pathlib,hashlib,json,zipfile
D=pathlib.Path(__file__).resolve().parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
before=json.loads((D/'frozen-before.json').read_text());after={};selected={}
base={'Defs.lean','Basic.lean','FortDuality.lean','KstFamily.lean','Core.lean','Remaining.lean'}
for lane in ['r1','r2b','r2a']:
 P=D.parent/('pdtar-formal-'+lane)
 Z=P/'pdtar-source.zip'
 assert sha(Z.read_bytes())==before[lane]['archive']
 with zipfile.ZipFile(Z) as z:
  modules={pathlib.PurePosixPath(n).name:sha(z.read(n)) for n in z.namelist() if n.startswith('PDTAR/') and n.endswith('.lean')}
 assert modules==before[lane]['modules']
 originals={n:sha((P/'PDTAR'/n).read_bytes()) for n in modules}
 assert originals==modules
 after[lane]=dict(archive=sha(Z.read_bytes()),modules=modules,original_sources=originals)
 for n,h in modules.items():
  use=n in base or (lane=='r2b' and n.startswith('Reduction')) or (lane=='r2a' and n not in base)
  if use:
   if n in selected:assert selected[n]==h
   selected[n]=h
for n,h in selected.items():assert sha((D/'PDTAR'/n).read_bytes())==h
assert len(selected)==23
(D/'frozen-after.json').write_text(json.dumps(after,indent=2)+'\n')
print('PASS: archives before/after, original sibling sources, 23 merged inherited modules; frozen base identical across all packets')
