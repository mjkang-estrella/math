"""Withdraw a resource-failed inherited candidate; resume exact position peeling."""
import sys
sys.dont_write_bytecode=True
import argparse,json,pathlib
H=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from peel import load,save,sha
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('prefix');a=ap.parse_args()
 large=load(H/'checks_large.json');t=load(H/'tree.json');lib=load(H/'library.json');ret=load(H/'withdrawn.json') if (H/'withdrawn.json').exists() else []
 for f,pair in large.items():
  if a.prefix not in pathlib.Path(f).name:continue
  assert pair['M']['result']=='PASS'
  assert pair['F5'].get('check',{}).get('problems')==['exception MemoryError: ']
  src=pathlib.Path(f);dst=H/'withdrawn'/src.name;dst.parent.mkdir(exist_ok=True)
  if src.exists():src.replace(dst)
  h=sha(dst);ids=[]
  for i,s in t['states'].items():
   if s.get('file')==f:
    s.update(status='PENDING',withdrawn_candidate=str(dst));s.pop('file',None);s.pop('sha256',None);ids.append(i)
  for r in lib:r['options']=[o for o in r['options'] if o['sha256']!=h]
  ret.append({'sha256':h,'withdrawn_file':str(dst),'former_file':f,'states':ids,'checks':pair,'reason':'F5 MemoryError at permitted 30000000 cap; replace with finer position partition'})
 save(H/'tree.json',t);save(H/'library.json',lib);save(H/'withdrawn.json',ret)
 print('withdrawn',[(r['withdrawn_file'],r['states']) for r in ret])
