#!/usr/bin/env python3
"""Read-only exact-member verification. No defaults for detached SHA256 anchors."""
import argparse,hashlib,json
from pathlib import Path,PurePosixPath
p=argparse.ArgumentParser()
p.add_argument('--packet',required=True);p.add_argument('--final',required=True);p.add_argument('--report',required=True)
p.add_argument('--manifest-sha256',required=True);p.add_argument('--final-sha256',required=True);p.add_argument('--report-sha256',required=True)
p.add_argument('--project',help='Optional read-only comparison of exact recorded original selections')
a=p.parse_args()
def sha(b):return hashlib.sha256(b).hexdigest()
def anchored(path,expected):
 b=Path(path).read_bytes();assert sha(b)==expected, 'detached anchor mismatch: '+str(path);return b
packet=Path(a.packet);mp=packet/'MANIFEST.json'
m=json.loads(anchored(mp,a.manifest_sha256));f=json.loads(anchored(a.final,a.final_sha256));anchored(a.report,a.report_sha256)
assert f['manifest_sha256']==a.manifest_sha256 and f['report_sha256']==a.report_sha256
assert f['packet_members']==len(m['members'])
expected=set()
for e in m['members']:
 s=e['path'];q=PurePosixPath(s)
 assert not q.is_absolute() and '..' not in q.parts and str(q)==s
 assert s not in expected and s!='MANIFEST.json';expected.add(s)
 path=packet/s;assert not path.is_symlink();b=path.read_bytes()
 assert len(b)==e['bytes'] and sha(b)==e['sha256'], 'member mismatch: '+s
actual=set()
for path in packet.rglob('*'):
 assert not path.is_symlink(), 'symlink not allowed'
 if path.is_file():actual.add(path.relative_to(packet).as_posix())
assert actual==expected|{'MANIFEST.json'}, 'exact membership mismatch'
source_bindings=0
ap=packet/'private/source-authentication.json'
if ap.exists():
 for e in json.loads(ap.read_text()):
  suffix=e['path'].split('/build/',1)[1];b=(packet/'private/source'/suffix).read_bytes()
  assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['blob']
  assert sha(b)==e['sha256'] and len(b)==e['bytes'];source_bindings+=1
original_comparisons=0
if a.project:
 project=Path(a.project)
 for e in json.loads((packet/'private/completed-exception-extents.json').read_text()):
  b=(project/e['original']).read_bytes();assert sha(b)==e['sha256']
  assert b[e['start']:e['end']]==(packet/e['local']).read_bytes();original_comparisons+=1
 for e in json.loads((packet/'private/history-extents.json').read_text()):
  b=(project/e['original']).read_bytes();assert sha(b)==e['original_sha256']
  assert b[e['start']:e['end']]==(packet/e['local']).read_bytes();original_comparisons+=1
print(json.dumps({'artifact_verification':'matched','members':len(expected),'source_blob_bindings':source_bindings,'original_selected_comparisons':original_comparisons,'mathematical_gate':False}))
