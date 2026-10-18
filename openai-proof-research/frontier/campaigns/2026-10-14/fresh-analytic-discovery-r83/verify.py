#!/usr/bin/env python3
"""r83 checkpoint identities only; no mathematical verification."""
import argparse,hashlib,json,stat
from pathlib import Path
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);ap.add_argument('--root',type=Path,default=Path(__file__).absolute().parent);ap.add_argument('--tree',type=Path,required=True);a=ap.parse_args();r=a.root
 assert len(a.anchor)==64 and all(c in '0123456789abcdef' for c in a.anchor),'bad anchor'
 for p in (r,*r.parents):assert not p.is_symlink(),'root symlink'
 assert sha(r/'manifest.json')==a.anchor,'external manifest mismatch';m=json.loads((r/'manifest.json').read_text());actual={}
 for p in r.rglob('*'):
  rel=str(p.relative_to(r));assert not p.is_symlink(),'symlink'
  if p.is_dir():continue
  assert stat.S_ISREG(p.stat().st_mode) and p.stat().st_nlink==1,'unsafe file'
  if not rel.startswith('private/') and rel!='manifest.json':actual[rel]=sha(p)
 assert actual==m['public_files'],'public inventory mismatch'
 tree={x['path']:x['sha'] for x in json.loads(a.tree.read_text())['tree'] if x['type']=='blob'}
 rec=json.loads((r/'source-receipts.json').read_text())
 for row in rec['files']:
  assert tree.get(row['path'])==row['git_blob'],'canonical membership mismatch'
  p=r/row['local'];data=p.read_bytes();assert sha(p)==row['sha256'],'private source changed'
  assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob'],'blob mismatch'
 s=json.loads((r/'scope-status.json').read_text());assert not s['full_proof_claim'] and not s['prospective_scope_frozen'] and not s['accepted'] and s['count_change']==0,'status overclaim'
 print(json.dumps({'status':'IDENTITY_ONLY','public_files':len(actual),'canonical_source_blobs':len(rec['files']),'nominee':False}))
if __name__=='__main__':main()
