"""Read-only exact-selection, detached-anchor, byte and mode verifier."""
from pathlib import Path
import argparse,hashlib,json,stat,sys
p=argparse.ArgumentParser()
p.add_argument('--packet',required=True);p.add_argument('--manifest-sha256',required=True)
p.add_argument('--final-sha256',required=True);p.add_argument('--report',required=True)
p.add_argument('--report-sha256',required=True)
a=p.parse_args();root=Path(a.packet);report=Path(a.report)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
try:
 need(not root.is_symlink() and root.is_dir(),'packet root type')
 manifest=root/'MANIFEST.json';final=root/'FINAL.md'
 for f,h in [(manifest,a.manifest_sha256),(final,a.final_sha256),(report,a.report_sha256)]:
  need(f.is_file() and not f.is_symlink(),'anchor target type: '+str(f));need(digest(f)==h,'detached anchor mismatch: '+str(f))
 data=json.loads(manifest.read_bytes());need(data['format']=='r229-exact-selection-v1','format')
 expect=data['entries'];need(len(expect)==len({e['path']for e in expect}),'duplicate path')
 actual={}
 for f in root.rglob('*'):
  need(not f.is_symlink(),'symlink: '+str(f));rel=f.relative_to(root).as_posix()
  if rel=='MANIFEST.json':continue
  actual[rel]=f
 need(set(actual)=={e['path']for e in expect},'exact selection mismatch')
 need(stat.S_IMODE(root.stat().st_mode)==int(data['root_mode'],8),'root mode')
 need(stat.S_IMODE(manifest.stat().st_mode)==0o400,'manifest mode')
 for e in expect:
  rel=e['path'];need(not Path(rel).is_absolute() and '..'not in Path(rel).parts,'unsafe manifest path')
  f=actual[rel];need(stat.S_IMODE(f.stat().st_mode)==int(e['mode'],8),'mode mismatch: '+rel)
  if e['type']=='directory':need(f.is_dir(),'directory type: '+rel)
  else:
   need(e['type']=='file' and f.is_file(),'file type: '+rel)
   need(f.stat().st_size==e['bytes'],'size mismatch: '+rel)
   need(digest(f)==e['sha256'],'content mismatch: '+rel)
 print(json.dumps({'artifact_verification':'exact selection, detached anchors, bytes and modes agree','files':sum(e['type']=='file'for e in expect),'directories':sum(e['type']=='directory'for e in expect),'mathematical_gate':False}))
except Exception as ex:
 print('ARTIFACT REJECTION: '+str(ex),file=sys.stderr);sys.exit(1)
