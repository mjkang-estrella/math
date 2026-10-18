#!/usr/bin/env python3
"""Exact public inventory and finite arithmetic only; no semantic acceptance.
Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""
import argparse,contextlib,hashlib,io,json,runpy
from pathlib import Path

def sha(b):return hashlib.sha256(b).hexdigest()
def verify(root,anchor):
 manifest=root/'MANIFEST.json'
 assert not manifest.is_symlink(),'manifest symlink'
 raw=manifest.read_bytes();assert sha(raw)==anchor,'external anchor mismatch'
 data=json.loads(raw);actual={}
 for p in root.iterdir():
  assert not p.is_symlink(),'symlink: '+p.name
  if p.name=='private':
   assert p.is_dir(),'private is not a directory'
   continue
  assert p.is_file(),'unexpected directory: '+p.name
  if p.name!='MANIFEST.json':actual[p.name]={'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}
 assert actual==data['files'],'inventory or content mismatch'
 output=io.StringIO()
 with contextlib.redirect_stdout(output):runpy.run_path(str(root/'diagnostics.py'),run_name='__main__')
 assert json.loads(output.getvalue())==json.loads((root/'diagnostics.json').read_text()),'diagnostic output mismatch'
 return {'status':'PASS','files':len(actual),'anchor':anchor,'scope':'public inventory and finite exact arithmetic only'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a=p.parse_args()
 try:print(json.dumps(verify(a.root,a.anchor),sort_keys=True))
 except (AssertionError,OSError,ValueError,KeyError) as e:
  print(json.dumps({'status':'FAIL','reason':str(e)}));raise SystemExit(1)
