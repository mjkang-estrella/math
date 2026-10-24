"""Read-only exact-selection/mode verifier. Supply all detached anchors explicitly."""
import argparse,hashlib,json,os,stat,sys
from pathlib import Path,PurePosixPath

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def require(ok,reason):
 if not ok:raise ValueError(reason)
def inspect(root):
 result={}
 def visit(p,rel):
  s=p.lstat();mode=stat.S_IMODE(s.st_mode)
  if stat.S_ISDIR(s.st_mode):
   result[rel]={'type':'directory','mode':format(mode,'04o')}
   for item in sorted(os.scandir(p),key=lambda x:x.name):
    visit(Path(item.path),item.name if rel=='.' else rel+'/'+item.name)
  elif stat.S_ISREG(s.st_mode):result[rel]={'type':'file','mode':format(mode,'04o'),'bytes':s.st_size,'sha256':sha(p)}
  else:raise ValueError('Non-regular or symbolic-link entry: '+rel)
 visit(root,'.');return result

def verify(packet,manifest,manifest_anchor,final_anchor,report,report_anchor):
 require(sha(manifest)==manifest_anchor,'Detached MANIFEST hash mismatch')
 m=json.loads(manifest.read_text())
 require(m['format']=='r210-exact-selected-packet-v1','Unknown manifest format')
 expected=m['entries'];require(len(expected)==len({x['path'] for x in expected}),'Duplicate selected path')
 for x in expected:
  p=PurePosixPath(x['path']);require(not p.is_absolute() and '..' not in p.parts,'Unsafe selected path')
 actual=inspect(packet)
 require(set(actual)=={x['path'] for x in expected},'Exact selection mismatch (extra or missing entry)')
 for x in expected:
  data={k:v for k,v in x.items() if k not in ['path','rights']}
  require(actual[x['path']]==data,'Entry hash/size/type/mode mismatch: '+x['path'])
 final=m['final'];require(final in actual and actual[final]['type']=='file','Missing FINAL')
 require(actual[final]['sha256']==final_anchor,'Detached FINAL hash mismatch')
 require(not report.resolve().is_relative_to(packet.resolve()),'REPORT must be outside selected packet')
 require(stat.S_ISREG(report.lstat().st_mode),'REPORT is not regular')
 require(stat.S_IMODE(report.lstat().st_mode)==0o644,'REPORT mode mismatch')
 require(sha(report)==report_anchor,'Detached REPORT hash mismatch')
 return {'verification':'exact selected bytes, types and modes match supplied detached anchors','files':sum(v['type']=='file' for v in actual.values()),'directories':sum(v['type']=='directory' for v in actual.values()),'FINAL_SHA256':final_anchor,'MANIFEST_SHA256':manifest_anchor,'REPORT_SHA256':report_anchor,'mathematical_gate':False}

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 for key in ['packet','manifest','manifest-sha256','final-sha256','report','report-sha256']:p.add_argument('--'+key,required=True)
 a=p.parse_args()
 try:print(json.dumps(verify(Path(a.packet),Path(a.manifest),a.manifest_sha256,a.final_sha256,Path(a.report),a.report_sha256),indent=2))
 except Exception as e:print(str(e),file=sys.stderr);sys.exit(1)
