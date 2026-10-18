#!/usr/bin/env python3
"""Read-only exact inventory verifier for independent AGM063 manuscript review. MIT.
Integrity only: no proof, reading, visual-inspection or acceptance certification.
"""
import argparse,hashlib,json,os,re,stat
from pathlib import Path,PurePosixPath
MANUSCRIPT='5a043ad5acdf541b9a10d912dbd0339b3c8c0aa2650bd92a4a41d5422d0c34bb'
PDF='bb9d911bf972f91d57f6e00b037ecd012e2cd892927d22ebbb5fa8ca0682b4b5'
def need(b,s):
 if not b:raise ValueError(s)
def sha(x):return hashlib.sha256(x).hexdigest()
def unique(pairs):
 d={}
 for k,v in pairs:need(k not in d,'duplicate JSON key');d[k]=v
 return d
def parse(x):return json.loads(x,object_pairs_hook=unique)
def safe(x):
 need(isinstance(x,str) and x and '\\' not in x and '\x00' not in x,'bad path')
 p=PurePosixPath(x);need(not p.is_absolute() and p.as_posix()==x and all(z not in ('..','.') for z in p.parts),'unsafe path')
 return x
def digest(x):return isinstance(x,str) and re.fullmatch('[0-9a-f]{64}',x) is not None
def verify(root,anchor):
 root=Path(os.path.abspath(root));need(root.is_dir(),'bad root')
 for p in [root,*root.parents]:need(not p.is_symlink(),'root ancestry symlink')
 need(digest(anchor),'bad anchor');p=root/'review-manifest.json';need(not p.is_symlink(),'manifest symlink')
 raw=p.read_bytes();need(sha(raw)==anchor,'external anchor mismatch');m=parse(raw)
 need(m['schema']=='AGM063-independent-manuscript-review-r1','schema')
 need(m['verdict']=='PASS_FULL_MANUSCRIPT_AGM063' and m['full_theorem_formalized'] is False,'scope')
 need(m['manuscript_manifest_sha256']==MANUSCRIPT and m['pdf_sha256']==PDF,'input pins')
 expected={}
 for row in m['files']:
  n=safe(row['path']);need(n not in expected and n!='review-manifest.json','duplicate/self path')
  need(type(row['bytes']) is int and row['bytes']>=0 and digest(row['sha256']),'file record');expected[n]=row
 wanted=[safe(n) for n in m['directories']];need(wanted==sorted(set(wanted)),'directory inventory')
 fs=set();ds=set()
 for folder,dirs,files in os.walk(root,followlinks=False):
  for name in dirs+files:
   p=Path(folder)/name;n=safe(p.relative_to(root).as_posix());st=p.lstat()
   need(not stat.S_ISLNK(st.st_mode),'symlink '+n)
   if stat.S_ISDIR(st.st_mode):ds.add(n)
   else:need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'nonregular/hardlink '+n);fs.add(n)
 need(fs==set(expected)|{'review-manifest.json'},'exact files');need(ds==set(wanted),'exact directories')
 for n,row in expected.items():
  raw=(root/n).read_bytes();need(len(raw)==row['bytes'] and sha(raw)==row['sha256'],'hash '+n)
 need(sha((root/'inputs/agm063-manuscript-r1-output-manifest.json').read_bytes())==MANUSCRIPT,'retained manuscript manifest')
 v=parse((root/'verdict.json').read_bytes());need(v['verdict']==m['verdict'] and v['full_theorem_formalized'] is False and not v['required_repairs'],'verdict binding')
 b=parse((root/'rebuild/checks/build-receipt.json').read_bytes());need(b['pdf_sha256']==PDF==sha((root/'rebuild/output/pdf/advanced-mukai-classification.pdf').read_bytes()),'PDF binding')
 for key,n in [('source_sha256','main.tex'),('formal_support_sha256','formal-support.tex')]:need(b[key]==sha((root/'rebuild'/n).read_bytes()),'source binding')
 visual=parse((root/'visual-review.json').read_bytes());need(visual['status']=='FINAL_ALL_PAGES_VISUALLY_INSPECTED' and visual['pdf_sha256']==PDF and visual['page_count']==9,'visual binding')
 need([x['page'] for x in visual['pages']]==list(range(1,10)),'page coverage')
 for row in visual['pages']:need(row['visually_inspected'] is True and sha((root/safe(row['path'])).read_bytes())==row['sha256'],'page binding')
 return dict(status='PASS_REVIEW_INTEGRITY_ONLY',payloads=len(fs)-1,directories=len(ds),writes=0,full_theorem_formalized=False)
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--anchor',required=True);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a=ap.parse_args()
 try:print(json.dumps(verify(a.root,a.anchor),sort_keys=True))
 except (ValueError,KeyError,TypeError,OSError) as e:print('INTEGRITY_REJECT: '+str(e));raise SystemExit(1)
