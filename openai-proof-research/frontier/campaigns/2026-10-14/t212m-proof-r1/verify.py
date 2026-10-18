#!/usr/bin/env python3
# Adapted from fresh-analytic-discovery-r74/verify.py
# (sha256 07e8bab03bb3eec56c9fff4c14642623686b09900902acee395b9939a8c95161,
# Copyright 2026 Myeongjin Kang, MIT) for the t212m-proof-r1 review record.
"""Externally anchored review-record identity and reviewed-byte binding; no mathematical verdict."""
import argparse,hashlib,json,os,stat
from pathlib import Path

VERDICTS={'PASS_FULL_T212M','FAIL_REQUIRED_GAPS'}

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
def regular(p):
 s=p.lstat();need(stat.S_ISREG(s.st_mode),'reviewed packet nonregular entry');return p.read_bytes()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);ap.add_argument('--packet')
 a=ap.parse_args();root=Path(__file__).absolute().parent
 need(len(a.anchor)==64 and all(c in '0123456789abcdef' for c in a.anchor),'malformed anchor')
 files,dirs=inspect(root);raw=(root/'manifest.json').read_bytes();need(sha(raw)==a.anchor,'external manifest mismatch');m=parse(raw)
 need(files==m['files'],'file inventory mismatch');need(dirs==m['directories'],'directory inventory mismatch')
 c=parse((root/'checks.json').read_bytes())
 need(c['verdict'] in VERDICTS,'unknown verdict')
 need((c['verdict']=='PASS_FULL_T212M')==(c['required_objections']==[]),'verdict inconsistency')
 need(c['accepted'] is False and c['published'] is False and c['count_change']==0,'campaign status mismatch')
 need(c['mathematical_verdict_certified_by_code'] is False,'code-certification claim')
 packet=Path(a.packet).absolute() if a.packet else root.parent/c['reviewed_packet']
 need(not packet.is_symlink() and packet.is_dir(),'reviewed packet missing')
 need(sha(regular(packet/'manifest.json'))==c['reviewed_packet_manifest_sha256'],'reviewed packet mismatch')
 for row in c['reviewed_files']:
  b=regular(packet/row['path']);need(sha(b)==row['sha256'] and len(b)==row['bytes'],'reviewed packet mismatch')
 print('IDENTITY PASS:',len(files),'review files;',len(c['reviewed_files']),'reviewed author/source files; recorded verdict',c['verdict'],'(not certified by code)')
if __name__=='__main__':
 try:main()
 except (OSError,ValueError,KeyError,TypeError) as e:raise SystemExit('REFUSED: '+str(e))
