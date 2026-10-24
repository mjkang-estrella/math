"""Read-only exact-selection verifier; detached anchors are mandatory CLI inputs."""
import argparse,hashlib,json,stat
from pathlib import Path,PurePosixPath

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def validate(root,manifest_sha,final_sha,report_sha):
 root=Path(root)
 for p,h in [(root/'MANIFEST.json',manifest_sha),(root/'packet/FINAL.md',final_sha),(root/'REPORT.md',report_sha)]:
  assert p.is_file() and not p.is_symlink(),f'not regular: {p}'
  assert digest(p)==h,f'detached anchor mismatch: {p.name}'
 m=json.loads((root/'MANIFEST.json').read_text());base=root/'packet';seenfiles=set();seendirs=set()
 def walk(p):
  assert not p.is_symlink(),'symlink in packet'
  if p.is_dir():
   seendirs.add(p.relative_to(base).as_posix())
   for z in p.iterdir():walk(z)
  else:
   assert stat.S_ISREG(p.stat().st_mode),'nonregular packet entry'
   seenfiles.add(p.relative_to(base).as_posix())
 walk(base)
 assert seenfiles==set(m['files']),'exact file selection differs'
 assert seendirs==set(m['directories']),'exact directory selection differs'
 for rel,e in m['files'].items():
  q=PurePosixPath(rel);assert not q.is_absolute() and '..' not in q.parts,'unsafe path'
  p=base/rel;s=p.stat();assert s.st_size==e['bytes'],f'size: {rel}'
  assert digest(p)==e['sha256'],f'hash: {rel}'
  assert format(stat.S_IMODE(s.st_mode),'04o')==e['mode'],f'mode: {rel}'
 for rel,mode in m['directories'].items():
  assert format(stat.S_IMODE((base/rel).stat().st_mode),'04o')==mode,f'directory mode: {rel}'
 return {'files':len(seenfiles),'directories':len(seendirs),'exact_selection_and_modes':'matched'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--final-sha256',required=True);p.add_argument('--report-sha256',required=True);a=p.parse_args()
 try:print(json.dumps(validate(a.root,a.manifest_sha256,a.final_sha256,a.report_sha256),sort_keys=True))
 except (AssertionError,OSError,ValueError,KeyError) as e:p.exit(1,str(e)+'\n')
