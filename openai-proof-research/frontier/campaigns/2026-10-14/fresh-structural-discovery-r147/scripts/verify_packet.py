"""Read-only exact packet verifier. All three trust anchors must be external."""
import argparse,hashlib,json,os,re,stat
from pathlib import Path

def digest(b):return hashlib.sha256(b).hexdigest()
def snapshot(root):
 files={};dirs=[]
 assert not root.is_symlink() and root.is_dir(),'root type'
 for base,ds,fs in os.walk(root,followlinks=False):
  for name in ds:
   p=Path(base)/name;s=p.lstat()
   assert stat.S_ISDIR(s.st_mode) and not p.is_symlink(),'non-directory/symlink'
   dirs.append(str(p.relative_to(root)))
  for name in fs:
   p=Path(base)/name;s=p.lstat()
   assert stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular/symlink/hardlink'
   b=p.read_bytes();files[str(p.relative_to(root))]={'size':len(b),'sha256':digest(b),'mode':stat.S_IMODE(s.st_mode)}
 return files,sorted(dirs)
def verify(root,anchors):
 for name,h in anchors.items():
  assert re.fullmatch('[0-9a-f]{64}',h),'anchor syntax'
  p=root/name;st=p.lstat()
  assert stat.S_ISREG(st.st_mode) and st.st_nlink==1,'envelope type'
  assert digest(p.read_bytes())==h,'external anchor '+name
 m=json.loads((root/'MANIFEST.json').read_text())
 assert set(m)=={'format','files','directories'} and m['format']=='r147-exact-v1','manifest schema'
 rows=m['files'];names=[x['path'] for x in rows]
 assert names==sorted(set(names)),'duplicate/order'
 assert m['directories']==sorted(set(m['directories'])),'directory duplicate/order'
 for name in names+m['directories']:
  p=Path(name)
  assert name and not p.is_absolute() and '..' not in p.parts and str(p)==name,'unsafe path'
 assert not set(names)&set(anchors),'envelopes in payload'
 actual,dirs=snapshot(root)
 for name in anchors:del actual[name]
 expected={}
 for row in rows:
  assert set(row)=={'path','size','sha256','mode'},'row schema'
  expected[row['path']]={k:row[k] for k in ('size','sha256','mode')}
 assert actual==expected,'exact payload membership/bytes/modes'
 assert dirs==m['directories'],'exact directory membership'
 return {'payloads':len(actual),'envelopes':len(anchors),'directories':len(dirs)}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root',type=Path)
 for name in ('final','manifest','report'):p.add_argument('--'+name,required=True)
 a=p.parse_args();print(json.dumps(verify(a.root,{'FINAL.md':a.final,'MANIFEST.json':a.manifest,'REPORT.md':a.report})))
