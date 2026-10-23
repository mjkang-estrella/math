#!/usr/bin/env python3
"""Read-only exact contribution-review packet verification with three mandatory detached anchors.
Implementation adapted from the admitted author verifier; selection manifest is new.
No manifest creation, repair, chmod, output-file writes, or inferred anchors.
"""
import argparse,hashlib,json,os,stat,sys
from pathlib import Path,PurePosixPath
sys.dont_write_bytecode=True

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()

def snapshot(packet):
 out=[]
 def rec(path,rel):
  st=path.lstat();mode=format(stat.S_IMODE(st.st_mode),'04o')
  if stat.S_ISLNK(st.st_mode):raise ValueError('symlink prohibited: '+rel)
  if stat.S_ISDIR(st.st_mode):
   out.append({'path':rel,'type':'directory','mode':mode})
   for entry in sorted(os.scandir(path),key=lambda e:e.name):
    rec(Path(entry.path),entry.name if not rel else rel+'/'+entry.name)
  elif stat.S_ISREG(st.st_mode):
   out.append({'path':rel,'type':'file','mode':mode,'size':st.st_size,'sha256':digest(path)})
  else:raise ValueError('nonregular selection: '+rel)
 rec(packet,'')
 return sorted(out,key=lambda e:e['path'])

def verify(packet,manifest,report,final_sha,manifest_sha,report_sha):
 for p in (packet,manifest,report):
  if p.is_symlink():raise ValueError('anchor path is symlink')
 for value in (final_sha,manifest_sha,report_sha):
  if len(value)!=64 or any(c not in '0123456789abcdef' for c in value):raise ValueError('literal SHA256 anchor required')
 if digest(manifest)!=manifest_sha:raise ValueError('MANIFEST detached anchor mismatch')
 if digest(report)!=report_sha:raise ValueError('outside REPORT detached anchor mismatch')
 if (packet/'FINAL.md').is_symlink():raise ValueError('FINAL is symlink')
 if digest(packet/'FINAL.md')!=final_sha:raise ValueError('FINAL detached anchor mismatch')
 m=json.loads(manifest.read_text())
 if m.get('format')!='structural-r203-contribution-r1-exact-v1' or m.get('packet_root')!=packet.name:raise ValueError('manifest selection identity mismatch')
 expected=m.get('entries')
 if not isinstance(expected,list):raise ValueError('manifest entry list missing')
 paths=[]
 for e in expected:
  rel=e['path'];pp=PurePosixPath(rel)
  if rel and (pp.is_absolute() or '..' in pp.parts or pp.as_posix()!=rel):raise ValueError('unsafe manifest path')
  paths.append(rel)
 if len(set(paths))!=len(paths):raise ValueError('duplicate manifest selection')
 actual=snapshot(packet)
 if actual!=sorted(expected,key=lambda e:e['path']):
  exp={e['path']:e for e in expected};act={e['path']:e for e in actual}
  detail={'missing':sorted(set(exp)-set(act)),'extra':sorted(set(act)-set(exp)),'changed':[p for p in sorted(set(exp)&set(act)) if exp[p]!=act[p]]}
  raise ValueError('exact selection/mode/bytes mismatch: '+json.dumps(detail))
 return {'verified':True,'files':sum(e['type']=='file' for e in actual),'directories':sum(e['type']=='directory' for e in actual),'meaning':'Artifact identity only; no mathematical verdict.'}

def main():
 a=argparse.ArgumentParser();a.add_argument('--packet',required=True,type=Path);a.add_argument('--manifest',required=True,type=Path);a.add_argument('--report',required=True,type=Path);a.add_argument('--final-sha256',required=True);a.add_argument('--manifest-sha256',required=True);a.add_argument('--report-sha256',required=True);v=a.parse_args()
 try:print(json.dumps(verify(v.packet,v.manifest,v.report,v.final_sha256,v.manifest_sha256,v.report_sha256),sort_keys=True))
 except Exception as e:print(str(e),file=sys.stderr);return 1
 return 0
if __name__=='__main__':sys.exit(main())
