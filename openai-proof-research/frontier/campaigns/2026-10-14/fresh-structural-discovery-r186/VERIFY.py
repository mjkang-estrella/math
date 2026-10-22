"""Read-only selected-packet verifier. Artifact integrity is not a mathematical gate."""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent
PROJECT=ROOT.parents[3]
def sha(b):return hashlib.sha256(b).hexdigest()
def read_local(name):
 p=ROOT/name
 assert not p.is_symlink(), ('symlink',name)
 assert p.resolve().is_relative_to(ROOT), ('outside root',name)
 return p.read_bytes()
def read_span(path,start,end):
 p=PROJECT/path
 assert not p.is_symlink()
 assert p.resolve().is_relative_to(PROJECT)
 with p.open('rb') as f:f.seek(start);return f.read(end-start)
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for n in ['final','manifest','report']:ap.add_argument('--'+n+'-sha',required=True)
 ap.add_argument('--originals',action='store_true');a=ap.parse_args()
 for name,want in [('FINAL.md',a.final_sha),('private/MANIFEST.json',a.manifest_sha),('REPORT.md',a.report_sha)]:
  assert len(want)==64 and sha(read_local(name))==want,('detached anchor',name)
 m=json.loads(read_local('private/MANIFEST.json'));names=[]
 for x in m['files']:
  b=read_local(x['path']);assert len(b)==x['bytes'] and sha(b)==x['sha256'],('payload',x['path']);names.append(x['path'])
 assert len(names)==len(set(names))
 assert {'FINAL.md','VERIFY.py','DERIVATIONS.md','INTERFACES.md','COMPARISON.md'}<=set(names)
 assert not {'private/MANIFEST.json','REPORT.md','ANCHORS.json'}&set(names)
 for x in json.loads(read_local('private/source310-authentication.json')):
  b=read_local(x['local']);assert sha(b)==x['sha256'];blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==x['git_blob']
 for x in json.loads(read_local('private/history-extents.json')):
  assert sha(read_local(x['local']))==x['sha256']
  if a.originals:assert sha(read_span(x['path'],x['start'],x['end']))==x['sha256']
 if a.originals:
  for x in json.loads(read_local('private/direct-input-anchors.json')):
   assert sha(read_span(x['path'],x['start'],x['end']))==x['sha256']
  for x in json.loads(read_local('private/completed-input-anchors.json')):
   assert sha(read_span(x['path'],0,x['bytes']))==x['sha256']
 c=json.loads(read_local('private/controls/expectations.json'))
 assert sha(read_local(c['original']))==c['expected_sha256']
 assert sha(read_local(c['copy']))==c['expected_sha256']
 assert sha(read_local(c['changed_copy']))!=c['expected_sha256']
 # Calculated identities are checked only against the stored bounded diagnostic;
 # this neither reruns mathematics nor turns the result into an acceptance gate.
 print(json.dumps({'artifact_integrity':'consistent','payload_files':len(names),'detached_anchors_checked':3,'canonical_git_blobs_checked':16,'copied_controls':'matching copy accepted; one-byte change detected','explicit_original_spans_checked':a.originals,'writes':0,'mathematical_grade':None}))
if __name__=='__main__':main()
