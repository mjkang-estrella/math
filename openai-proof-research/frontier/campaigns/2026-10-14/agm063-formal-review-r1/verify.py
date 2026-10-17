#!/usr/bin/env python3
"""Read-only AGM063 review exact-inventory verifier. MIT; integrity only."""
import argparse,hashlib,json,os,re,stat
from pathlib import Path,PurePosixPath
PIN='ca6bdb0cccd691d0c8a94ff8ec3bfbd9ccdd87a64ba5b4cf344a1b1c73b8ad9c'
def need(b,s):
 if not b:raise ValueError(s)
def sha(x):return hashlib.sha256(x).hexdigest()
def unique(pairs):
 d={}
 for k,v in pairs:need(k not in d,'duplicate JSON key');d[k]=v
 return d
def parse(x):return json.loads(x,object_pairs_hook=unique)
def safe(x):
 need(isinstance(x,str) and x and '\\' not in x,'bad path')
 p=PurePosixPath(x);need(not p.is_absolute() and p.as_posix()==x and all(z not in ('..','.') for z in p.parts),'unsafe path')
 return x
def verify(root,anchor):
 need(re.fullmatch('[0-9a-f]{64}',anchor) is not None,'bad anchor')
 need(root.is_dir() and not root.is_symlink(),'bad root')
 p=root/'review-manifest.json';need(not p.is_symlink(),'manifest symlink');raw=p.read_bytes();need(sha(raw)==anchor,'external anchor mismatch');m=parse(raw)
 need(m['schema']=='AGM063-independent-formal-review-r1','schema')
 need(m['verdict']=='PASS_SCOPED_SUPPORT' and m['full_theorem_formalized'] is False,'scope')
 need(m['implementation_anchor']==PIN,'implementation anchor')
 expected={}
 for row in m['files']:
  n=safe(row['path']);need(n not in expected and n!='review-manifest.json','duplicate/self path');expected[n]=row
 wanted=[safe(n) for n in m['directories']];need(len(wanted)==len(set(wanted)),'duplicate directories')
 fs=set();ds=set()
 for folder,dirs,files in os.walk(root,followlinks=False):
  for name in dirs+files:
   p=Path(folder)/name;n=safe(p.relative_to(root).as_posix());mode=p.lstat().st_mode
   need(not stat.S_ISLNK(mode),'symlink '+n)
   if stat.S_ISDIR(mode):ds.add(n)
   else:need(stat.S_ISREG(mode),'nonregular '+n);fs.add(n)
 need(fs==set(expected)|{'review-manifest.json'},'exact files');need(ds==set(wanted),'exact directories')
 for n,row in expected.items():
  raw=(root/n).read_bytes();need(len(raw)==row['bytes'] and sha(raw)==row['sha256'],'hash '+n)
 need(sha((root/'rebuild-copy/output-manifest.json').read_bytes())==PIN,'retained implementation identity')
 a=parse((root/'declaration-audit.json').read_bytes());need(len(a['declarations'])==35 and a['full_theorem_formalized'] is False,'audit inventory')
 b=parse((root/'rebuild-copy/review-build/receipt.json').read_bytes());need(b['status'].startswith('PASS scoped source build'),'build status')
 need(set(x['declaration'] for x in a['declarations'])==set('AGM063.'+n for n in b['support_declarations']),'declaration inventory')
 return dict(result='PASS_REVIEW_INTEGRITY_ONLY',payloads=len(fs)-1,directories=len(ds),writes=0,full_theorem_formalized=False)
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--anchor',required=True);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a=ap.parse_args()
 try:print(json.dumps(verify(a.root.absolute(),a.anchor),sort_keys=True))
 except (ValueError,KeyError,TypeError,OSError) as e:print('INTEGRITY_REJECT: '+str(e));raise SystemExit(1)
