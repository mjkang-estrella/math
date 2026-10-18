#!/usr/bin/env python3
"""Authenticate and stage an incomplete public selection; no release gate. MIT."""
import argparse,hashlib,json,stat,sys
from pathlib import Path,PurePosixPath
HERE=Path(__file__).absolute().parent
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def require(ok,why):
 if not ok:raise ValueError(why)
def sha(data):return hashlib.sha256(data).hexdigest()
def read(root,name):
 parts=PurePosixPath(name).parts;require(parts and not name.startswith('/') and '..' not in parts,'unsafe path')
 p=root
 for part in parts:
  p=p/part;require(not p.is_symlink(),'symlink path')
 require(p.is_file() and p.stat().st_nlink==1,'nonregular or hardlinked file')
 return p.read_bytes()
def authenticate(anchor):
 require(len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor),'malformed preparation anchor')
 raw=read(HERE,'manifest.json');require(sha(raw)==anchor,'preparation external anchor mismatch');m=json.loads(raw)
 actual={str(p.relative_to(HERE)):sha(read(HERE,str(p.relative_to(HERE)))) for p in HERE.rglob('*') if not p.is_dir() and p.name!='manifest.json'}
 require(actual==m['files'],'preparation exact files mismatch');require(sorted(str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_dir())==m['directories'],'preparation directories mismatch')
 return json.loads(read(HERE,'public-selection.json'))
def validate(root,s):
 require(s['final_manuscript_review_anchor'] is None and not s['accepted'] and not s['published'] and s['count_change']==0 and not s['full_theorem_formalized'],'preparation status changed')
 manifests={}
 for packet,a in s['anchors'].items():
  raw=read(root,packet+'/'+a['manifest']);require(sha(raw)==a['sha256'],'frozen manifest anchor mismatch');manifests[packet]=json.loads(raw)
 names=set()
 for r in s['files']:
  name=r['path'];require(name not in names,'duplicate selection');names.add(name)
  require(not any(x in PurePosixPath(name).parts for x in ['private','.lake','__pycache__']),'excluded body/cache')
  require(not name.endswith(('run_review.py','review_controls.py','seal.py')),'write-in-place driver')
  data=read(root,name);require(sha(data)==r['sha256'] and len(data)==r['bytes'],'selected bytes changed')
  packet=r['packet']
  if packet and r['relative']!=s['anchors'][packet]['manifest']:
   records=manifests[packet]['files']
   if isinstance(records,list):records={x['path']:x for x in records}
   rec=records.get(r['relative']);expected=rec if isinstance(rec,str) else rec.get('sha256') if rec else None
   require(expected==r['sha256'],'selected bytes not frozen members')
 return names
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);ap.add_argument('--campaign',type=Path,required=True);ap.add_argument('--output',type=Path);a=ap.parse_args()
 s=authenticate(a.anchor);names=validate(a.campaign,s)
 if a.output:
  a.output.mkdir(parents=True,exist_ok=False)
  for name in sorted(names):
   f=a.output/name;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(read(a.campaign,name))
  (a.output/'PREPARATION-NOT-RELEASE.txt').write_text('Incomplete preparation only. Manuscript review and final external gate are absent. No acceptance/publication.\n')
  validate(a.output,s)
 print(json.dumps({'status':'PASS_SELECTION_IDENTITY_ONLY','selected_files':len(names),'anchors':len(s['anchors']),'final_manuscript_review_anchor':None,'ready_for_release':False}))
if __name__=='__main__':
 try:main()
 except (ValueError,OSError,KeyError,TypeError) as e:sys.exit('REFUSED: '+str(e))
