#!/usr/bin/env python3
"""Read-only verification; all trust anchors must be supplied explicitly."""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def main():
 a=argparse.ArgumentParser()
 for n in ('packet','manifest','selection','report','final-sha','manifest-sha','selection-sha','report-sha'):
  a.add_argument('--'+n,required=True)
 x=a.parse_args();p=Path(x.packet);m=Path(x.manifest);s=Path(x.selection);r=Path(x.report)
 need(not p.is_symlink() and p.is_dir(),'unsafe packet root')
 need(stat.S_IMODE(p.stat().st_mode)==0o700,'packet-root mode differs')
 for f,h in [(m,x.manifest_sha),(s,x.selection_sha),(r,x.report_sha),(p/'FINAL.md',x.final_sha)]:
  need(not f.is_symlink() and f.is_file(),'unsafe anchored file')
  need(digest(f)==h,'detached anchor mismatch: '+f.name)
 manifest=json.loads(m.read_text()); selection=json.loads(s.read_text())
 need(manifest['selection_sha256']==x.selection_sha,'selection binding mismatch')
 entries=manifest['entries']; paths=[e['path'] for e in entries]
 need(len(paths)==len(set(paths)),'duplicate entries')
 need([{'path':e['path'],'kind':e['kind'],'mode':e['mode']} for e in entries]==selection,'manifest selection differs')
 actual=[]
 for directory,ds,fs in os.walk(p,followlinks=False):
  for n in ds+fs:
   q=Path(directory)/n;need(not q.is_symlink(),'symlink in packet')
   actual.append(q.relative_to(p).as_posix())
 need(sorted(actual)==sorted(paths),'extra or missing packet entries')
 for e in entries:
  rel=PurePosixPath(e['path']);need(not rel.is_absolute() and '..' not in rel.parts and rel.as_posix()==e['path'],'unsafe selected path')
  q=p/e['path']; st=q.stat();need(format(stat.S_IMODE(st.st_mode),'04o')==e['mode'],'mode mismatch: '+e['path'])
  if e['kind']=='dir':need(q.is_dir(),'directory kind mismatch')
  else:
   need(e['kind']=='file' and q.is_file(),'file kind mismatch')
   need(st.st_size==e['bytes'] and digest(q)==e['sha256'],'content mismatch: '+e['path'])
 print(json.dumps({'artifact_verification':'matches explicit anchors, exact selection, modes and bytes','entries':len(entries),'files':sum(e['kind']=='file' for e in entries),'mathematical_gate':False}))
if __name__=='__main__':
 try:main()
 except (ValueError,OSError,KeyError,json.JSONDecodeError) as e:
  print('REJECTED: '+str(e));raise SystemExit(1)
