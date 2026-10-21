"""Read-only packet verifier. Explicit external anchors are mandatory. No math gates."""
from pathlib import Path
import argparse,hashlib,json,os,re,sys
ENVELOPES={'MANIFEST.json','REPORT.md','FINAL.md'}
def digest(data):return hashlib.sha256(data).hexdigest()
def inventory(root):
 files={};dirs=[]
 for here,names,leaves in os.walk(root,followlinks=False):
  for name in names:
   p=Path(here)/name
   if p.is_symlink():raise ValueError('symlink directory')
   dirs.append(p.relative_to(root).as_posix())
  for name in leaves:
   p=Path(here)/name
   if p.is_symlink() or not p.is_file():raise ValueError('nonregular payload')
   rel=p.relative_to(root).as_posix()
   if rel in ENVELOPES:continue
   b=p.read_bytes();files[rel]={'size':len(b),'sha256':digest(b)}
 return {'files':dict(sorted(files.items())),'directories':sorted(dirs)}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True)
 for n in ['manifest','report','final']:ap.add_argument('--'+n+'-sha',required=True)
 a=ap.parse_args();root=Path(a.root).resolve()
 for name,expected in [('MANIFEST.json',a.manifest_sha),('REPORT.md',a.report_sha),('FINAL.md',a.final_sha)]:
  if not re.fullmatch('[0-9a-f]{64}',expected):raise ValueError('invalid detached anchor')
  p=root/name
  if p.is_symlink() or not p.is_file():raise ValueError('missing/nonregular envelope')
  if digest(p.read_bytes())!=expected:raise ValueError('external anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_bytes())
 if m.get('schema')!='r139-exact-payload-v1' or m.get('excluded_root_envelopes')!=sorted(ENVELOPES):raise ValueError('manifest schema')
 for rel in m['inventory']['files']:
  p=Path(rel)
  if p.is_absolute() or '..' in p.parts or p.as_posix()!=rel or rel in ENVELOPES:raise ValueError('unsafe payload path')
 if inventory(root)!=m['inventory']:raise ValueError('payload bytes or exact membership mismatch')
 report=(root/'REPORT.md').read_text();final=(root/'FINAL.md').read_text()
 if a.manifest_sha not in report or a.manifest_sha not in final or a.report_sha not in final:raise ValueError('envelope cross binding mismatch')
 print(json.dumps({'artifact_integrity':'verified','payload_files':len(m['inventory']['files']),'directories':len(m['inventory']['directories']),'read_only':True,'mathematical_verdict':None}))
if __name__=='__main__':
 try:main()
 except Exception as e:print(str(e),file=sys.stderr);sys.exit(1)
