"""Offline package integrity and actual safe-extraction test; never executes Lean."""
import pathlib,hashlib,tarfile,shutil,resource,os,json
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(1900000000,1900000000))
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
D=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for line in (D/'MANIFEST.sha256').read_text().splitlines():
 h,name=line.split('  ',1);p=pathlib.PurePosixPath(name)
 assert not p.is_absolute() and '..' not in p.parts
 assert sha(D/name)==h,name
assert sha(D/'lean-packet.tar.gz')=='9f16ff5afa9a23b693443c0916507a8103bef5f23e431ca6c39e8cb4e7318200'
test=D/'packet-retest'
assert not test.exists()
test.mkdir()
try:
 with tarfile.open(D/'lean-packet.tar.gz','r:gz') as tf:
  ms=tf.getmembers();assert len(ms)==3
  assert {m.name for m in ms}=={'Definitions.lean','Witness.lean','Audit.lean'}
  for m in ms:
   assert m.isfile() and not m.issym() and not m.islnk() and 0<m.size<1000000
   with (test/m.name).open('xb') as f:f.write(tf.extractfile(m).read())
   assert sha(test/m.name)==sha(D/'packet-safe-extracted'/m.name)
finally:shutil.rmtree(test)
print('PASS: full manifest and fresh safe extraction; no formal code executed')
