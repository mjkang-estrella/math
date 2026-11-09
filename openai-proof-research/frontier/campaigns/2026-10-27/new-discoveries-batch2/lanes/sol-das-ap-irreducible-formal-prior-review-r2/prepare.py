from pathlib import Path
import json,hashlib,shutil,gzip,tarfile,io
B=Path(__file__).resolve().parent; E=B/'extracted'; R=B/'replay';R.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n in ['Definitions.lean','Witness.lean','pins.json','verify_pins.py']:shutil.copyfile(E/n,R/n)
# The helper's AS limit continues to apply to this guard. Lean itself has the
# separately authorized -M2700/groupRSS2800 budget and no additional AS cap.
s=(E/'lean_guard.py').read_text().replace('def pre():resource.setrlimit(resource.RLIMIT_CPU,(210,210))','def pre():\n resource.setrlimit(resource.RLIMIT_AS,(resource.RLIM_INFINITY,resource.RLIM_INFINITY))\n resource.setrlimit(resource.RLIMIT_CPU,(210,210))')
(R/'lean_guard.py').write_text(s)
a=(E/'Audit.lean').read_text().replace('DECL|{n}|ORIGIN|{origin}|UNSAFE|{info.isUnsafe}', 'DECL|{n}|ORIGIN|{origin}|UNSAFE|{info.isUnsafe}')
(R/'IndependentAudit.lean').write_text(a)
# Recreate deterministic bytes from archive members rather than run worker packaging.
with tarfile.open(B/'frozen/source-only.tar.gz') as tf:
 members=tf.getmembers();buf=io.BytesIO()
 with tarfile.open(fileobj=buf,mode='w',format=tarfile.USTAR_FORMAT) as out:
  for m in members:
   assert m.isfile() and m.uid==m.gid==m.mtime==0 and m.mode==0o644 and m.uname==m.gname==''
   assert not m.name.endswith(('.olean','.ilean','.so','.o','.pyc'))
   raw=(E/m.name).read_bytes();out.addfile(m,io.BytesIO(raw))
 assert [m.name for m in members]==sorted(m.name for m in members)
 rebuilt=gzip.compress(buf.getvalue(),mtime=0)
 assert rebuilt==(B/'frozen/source-only.tar.gz').read_bytes()
 sm=json.loads((E/'source-manifest.json').read_text())
 assert set(sm)==set(m.name for m in members)-{'source-manifest.json'}
 for n,h in sm.items():assert sha(E/n)==h
original_pairs=[]
for row in json.loads((E/'freeze.json').read_text()):
 print(row)
(B/'archive-check.json').write_text(json.dumps({'deterministic_byte_identity':True,'members':len(members),'source_manifest_all_members':True},indent=2))
