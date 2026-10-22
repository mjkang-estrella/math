#!/usr/bin/env python3
"""Read-only byte/mode verifier. Three detached anchors are mandatory.
This verifies artifacts, not mathematical claims. No writes or network access.
"""
import argparse,hashlib,json,stat
from pathlib import Path

def digest(b): return hashlib.sha256(b).hexdigest()
def inside(root,name):
 p=Path(name)
 assert not p.is_absolute() and '..' not in p.parts, 'unsafe path'
 q=root/p
 assert not q.is_symlink() and q.resolve().is_relative_to(root.resolve()), 'symlink/escape'
 return q

def main():
 a=argparse.ArgumentParser(description=__doc__)
 a.add_argument('--root',required=True)
 a.add_argument('--final-sha256',required=True)
 a.add_argument('--manifest-sha256',required=True)
 a.add_argument('--report-sha256',required=True)
 a.add_argument('--original-project')
 o=a.parse_args();r=Path(o.root)
 for name,want in [('FINAL.md',o.final_sha256),('MANIFEST.json',o.manifest_sha256),('REPORT.md',o.report_sha256)]:
  assert len(want)==64 and digest(inside(r,name).read_bytes())==want, name+' detached anchor mismatch'
 manifest=json.loads((r/'MANIFEST.json').read_text()); entries=manifest['files']; names=set()
 for e in entries:
  name=e['path']; assert name not in names;names.add(name);p=inside(r,name);b=p.read_bytes()
  assert len(b)==e['bytes'] and digest(b)==e['sha256'],name+' payload mismatch'
  assert stat.S_IMODE(p.stat().st_mode)==e['mode'],name+' mode mismatch'
 assert 'FINAL.md' in names and not (names & {'MANIFEST.json','REPORT.md','ANCHORS.json'})
 actual=set()
 for p in r.rglob('*'):
  assert not p.is_symlink(),'symlink in packet'
  if p.is_file():actual.add(p.relative_to(r).as_posix())
 assert actual==names|{'MANIFEST.json','REPORT.md','ANCHORS.json'}, 'unexpected/missing file inventory'
 anchors=json.loads((r/'ANCHORS.json').read_text())
 assert anchors=={'FINAL.md':o.final_sha256,'MANIFEST.json':o.manifest_sha256,'REPORT.md':o.report_sha256}
 extra={}
 if o.original_project:
  project=Path(o.original_project)
  originals=json.loads((r/'private/original-extents.json').read_text())
  for e in originals:
   p=inside(project,e['path'])
   with p.open('rb') as f:f.seek(e['start']);b=f.read(e['end']-e['start'])
   assert len(b)==e['end']-e['start'] and digest(b)==e['sha256'], 'original range changed: '+e['path']
   assert inside(r,e['copy']).read_bytes()==b,'range copy mismatch'
  tree=(project/'sources/preprints-tree.json').read_bytes()
  assert len(tree)==4858136 and digest(tree)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
  entries=json.loads(tree)['tree'];assert len(entries)==13223
  bypath={e['path']:e for e in entries}
  bindings=json.loads((r/'private/source-bindings.json').read_text())
  assert len(bindings)==11
  for e in bindings:
   b=inside(r,'private/canonical/'+e['path'].split('/build/',1)[1]).read_bytes()
   blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
   assert len(b)==e['size']==bypath[e['path']]['size']
   assert blob==e['sha']==bypath[e['path']]['sha'] and digest(b)==e['sha256']
  extra={'original_ranges':len(originals),'canonical_git_bindings':len(bindings)}
 print(json.dumps({'artifact_match':True,'payload_files':len(names),**extra}))
if __name__=='__main__':main()
