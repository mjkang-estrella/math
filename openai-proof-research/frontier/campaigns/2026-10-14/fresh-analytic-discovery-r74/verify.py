#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Externally anchored exact packet identity; no mathematical verdict."""
import argparse,hashlib,json,os,stat
from pathlib import Path

def sha(b):return hashlib.sha256(b).hexdigest()
def need(v,s):
 if not v:raise ValueError(s)
def pairs(rows):
 d={}
 for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
 return d
def parse(b):return json.loads(b,object_pairs_hook=pairs)
def inspect(root):
 need(not root.is_symlink() and not any(p.is_symlink() for p in root.parents),'symlink root ancestry')
 files={};dirs=[]
 for base,ds,fs in os.walk(root):
  for name in ds+fs:
   p=Path(base)/name;s=p.lstat();r=str(p.relative_to(root))
   need(not stat.S_ISLNK(s.st_mode),'symlink entry')
   if stat.S_ISDIR(s.st_mode):dirs.append(r);continue
   need(stat.S_ISREG(s.st_mode),'nonregular entry');need(s.st_nlink==1,'hardlink entry')
   if r!='manifest.json':b=p.read_bytes();files[r]={'bytes':len(b),'sha256':sha(b)}
 return files,sorted(dirs)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);a=ap.parse_args();root=Path(__file__).absolute().parent
 files,dirs=inspect(root);raw=(root/'manifest.json').read_bytes();need(sha(raw)==a.anchor,'external manifest mismatch');m=parse(raw)
 need(files==m['files'],'file inventory mismatch');need(dirs==m['directories'],'directory inventory mismatch')
 src=parse((root/'source-receipts.json').read_bytes());need(src['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','source pin')
 for row in src['files']:
  b=(root/row['local']).read_bytes();need(sha(b)==row['sha256'] and len(b)==row['bytes'],'source receipt mismatch')
  need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob'],'source blob mismatch')
 for row in parse((root/'primary-receipts.json').read_bytes()):
  b=(root/row['path']).read_bytes();need(sha(b)==row['sha256'] and len(b)==row['bytes'],'primary receipt mismatch')
 for row in parse((root/'parent-author-provenance.json').read_bytes()):
  need(sha((root/row['snapshot']).read_bytes())==row['sha256'],'author snapshot mismatch')
 c=parse((root/'checkpoint.json').read_bytes());a=parse((root/'author-completion.json').read_bytes())
 need(c['accepted'] is False and c['published'] is False and c['count_change']==0,'campaign status mismatch')
 need(c['independent_review'] is None and a['independent_proof_review'] is None and a['independent_contribution_review'] is None,'unearned review claim')
 need(a['target']==parse((root/'scope-status.json').read_bytes())['target'],'changed full target')
 need(c['author_full_proof_claim'] is True and c['full_target_proved'] is False,'author versus independent status mismatch')
 print('IDENTITY PASS:',len(files),'files; no mathematical verdict')
if __name__=='__main__':
 try:main()
 except (OSError,ValueError,KeyError,TypeError) as e:raise SystemExit('REFUSED: '+str(e))
