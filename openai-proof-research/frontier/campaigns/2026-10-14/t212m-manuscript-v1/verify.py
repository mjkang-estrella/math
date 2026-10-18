#!/usr/bin/env python3
"""Exact manuscript identity checks only. Myeongjin Kang; MIT."""
import argparse,hashlib,json,re,stat
from pathlib import Path
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,why):
 if not ok:raise ValueError(why)
def verify(root,anchor,campaign):
 require(re.fullmatch('[0-9a-f]{64}',anchor),'malformed anchor')
 for x in (root,*root.parents):require(not x.is_symlink(),'symlink root ancestry')
 require(sha(root/'manifest.json')==anchor,'external manifest mismatch')
 m=json.loads((root/'manifest.json').read_text());files={};dirs=[]
 for p in sorted(root.rglob('*')):
  mode=p.lstat().st_mode;require(not stat.S_ISLNK(mode),'symlink entry')
  rel=str(p.relative_to(root))
  if stat.S_ISDIR(mode):dirs.append(rel);continue
  require(stat.S_ISREG(mode),'nonregular entry');require(p.stat().st_nlink==1,'hardlink entry')
  if rel!='manifest.json':files[rel]=sha(p)
 require(files==m['files'],'file inventory mismatch');require(dirs==m['directories'],'directory inventory mismatch')
 q=json.loads((root/'provenance.json').read_text())
 require(q['accepted'] is False and q['published'] is False and q['count_change']==0 and q['manuscript_review'] is None and q['full_theorem_formalized'] is False,'status claim')
 for r in q['evidence']:
  require(sha(root/r['selected'])==r['sha256'],'selected evidence mismatch')
  p=campaign/r['source'];require(p.is_file() and not p.is_symlink() and p.stat().st_nlink==1,'upstream nonregular or missing')
  require(sha(p)==r['sha256'],'upstream evidence mismatch')
 receipts=[json.loads((root/f'validation/{x}-build-receipt.json').read_text()) for x in ('b','c')]
 pdf=sha(root/'public/manuscript.pdf')
 require(all(r['exit_code']==0 and r['pdf_sha256']==pdf for r in receipts),'build receipt mismatch')
 sources={str(p.relative_to(root)):sha(p) for p in sorted((root/'public').rglob('*.tex'))}
 require(all(r['sources']==sources for r in receipts),'source build mismatch')
 require(all('Warning' not in (root/f'validation/{x}-main.log').read_text() and 'Overfull' not in (root/f'validation/{x}-main.log').read_text() for x in ('b','c')),'typesetting warning')
 return {'status':'PASS_IDENTITY_ONLY','payloads':len(files),'directories':len(dirs),'pdf_sha256':pdf,'mathematical_verdict':None}
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).absolute().parent);p.add_argument('--anchor',required=True);p.add_argument('--repository-campaign',type=Path,required=True);a=p.parse_args()
 try:print(json.dumps(verify(a.root.absolute(),a.anchor,a.repository_campaign.absolute()),indent=2))
 except (ValueError,OSError,KeyError) as e:raise SystemExit('REJECT: '+str(e))
if __name__=='__main__':main()
