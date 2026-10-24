"""Read-only verification of the exact locally selected r230 packet.
Requires three explicit detached SHA256 anchors. Does not run mathematics.
"""
from pathlib import Path
import argparse,hashlib,json,re,stat
def sha(b):return hashlib.sha256(b).hexdigest()
def verify(root,anchors):
 root=Path(root)
 assert root.is_absolute() and root.is_dir() and not root.is_symlink(),'root'
 for key,name in [('final','FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]:
  expected=anchors[key]
  assert re.fullmatch(r'[0-9a-f]{64}',expected),'explicit anchor syntax'
  p=root/name
  assert p.is_file() and not p.is_symlink(),'anchor file type'
  assert sha(p.read_bytes())==expected,'detached '+key+' anchor mismatch'
 m=json.loads((root/'MANIFEST.json').read_bytes())
 assert m['schema']=='r230-exact-selection-v1','schema'
 entries=m['files'];paths=[e['path'] for e in entries]
 assert paths==sorted(set(paths)) and 'FINAL.md' in paths,'sorted exact selection'
 selection=sha(('\n'.join(paths)+'\n').encode())
 assert selection==m['selection_sha256'],'selection path digest mismatch'
 text=(root/'FINAL.md').read_text()
 assert 'Selection SHA256: '+selection in text,'FINAL selection mismatch'
 for e in entries:
  rel=e['path'];parts=Path(rel).parts
  assert rel and not Path(rel).is_absolute() and '..' not in parts and rel==Path(rel).as_posix(),'unsafe path'
  assert rel not in ['MANIFEST.json','REPORT.md','ANCHORS.json'],'detached file selected'
  p=root
  for part in parts:
   p=p/part
   assert not p.is_symlink(),'selected symlink'
  st=p.stat()
  assert stat.S_ISREG(st.st_mode),'selected nonregular file'
  assert e['mode']=='0444' and stat.S_IMODE(st.st_mode)==0o444,'selected mode mismatch: '+rel
  b=p.read_bytes()
  assert len(b)==e['bytes'] and sha(b)==e['sha256'],'selected byte/hash mismatch: '+rel
 return {'artifact_verification':'PASS','selected_files':len(entries),'selection_sha256':selection,'mode':'read-only; no mathematical gate'}
if __name__=='__main__':
 ap=argparse.ArgumentParser()
 ap.add_argument('root');ap.add_argument('--final-sha256',required=True);ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--report-sha256',required=True)
 args=ap.parse_args()
 try:print(json.dumps(verify(args.root,{'final':args.final_sha256,'manifest':args.manifest_sha256,'report':args.report_sha256}),sort_keys=True))
 except Exception as e:raise SystemExit('ARTIFACT VERIFICATION FAILED: '+str(e))
