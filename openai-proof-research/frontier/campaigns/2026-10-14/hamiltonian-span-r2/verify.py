#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Authenticate first; replay only read-only local code; never write any file."""
import argparse,hashlib,json,os,subprocess,sys
from pathlib import Path,PurePosixPath
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
R6=ROOT.parent/'fresh-structural-discovery-r6'
R6_ANCHOR='8cd0210428791a68f2e0a10b9447217996fb3a45967cc3b4203bca51ba647921'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
CONTROL={'seal.json','seal.sha256','inputs-manifest.json','outputs-manifest.json'}
def sha(b):return hashlib.sha256(b).hexdigest()
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def read_safe(root,name):
 p=PurePosixPath(name)
 require(not p.is_absolute() and '..' not in p.parts and str(p)==name and name not in ('','.'),'unsafe path')
 f=root.joinpath(*p.parts)
 require(not f.is_symlink() and all(not q.is_symlink() for q in f.parents if q!=root.parent),'symlink rejected')
 require(f.is_file(),'not regular file: '+name)
 return f.read_bytes()
def record(b):return {'size':len(b),'sha256':sha(b)}
def snapshot(root):
 result={}
 for f in sorted(root.rglob('*')):
  require(not f.is_symlink(),'symlink in tree')
  if f.is_file():result[f.relative_to(root).as_posix()]=record(f.read_bytes())
 return result

def authenticate(anchor):
 raw=read_safe(ROOT,'seal.json');require(sha(raw)==anchor,'detached seal authentication failed')
 seal=json.loads(raw)
 require(seal['status']=='UNRESOLVED' and seal['counted'] is False,'scope/status mismatch')
 require(read_safe(ROOT,'seal.sha256').decode().strip()==anchor,'detached anchor file mismatch')
 expected={};counts=[]
 for kind,name in [('input','inputs-manifest.json'),('output','outputs-manifest.json')]:
  raw=read_safe(ROOT,name);require(record(raw)==seal['manifests'][name],'manifest authentication failed: '+name)
  mf=json.loads(raw);require(mf['kind']==kind,'manifest kind mismatch');counts.append(len(mf['files']))
  for e in mf['files']:
   path=e['path'];require(path not in expected and path not in CONTROL,'duplicate/control entry')
   require(path.startswith('inputs/')==(kind=='input'),'input/output split mismatch')
   b=read_safe(ROOT,path);require(record(b)=={k:e[k] for k in ['size','sha256']},'file authentication failed: '+path)
   expected[path]=record(b)
 actual=snapshot(ROOT);require(set(actual)==set(expected)|CONTROL,'exact inventory mismatch')
 # Reauthenticate copied r6 controls and their relationship to copied context.
 old=read_safe(ROOT,'inputs/private/r6-seal.json');require(sha(old)==R6_ANCHOR,'r6 copied seal mismatch');oldseal=json.loads(old)
 require(read_safe(ROOT,'inputs/private/r6-seal.sha256').decode().strip()==R6_ANCHOR,'r6 copied detached anchor mismatch')
 old_entries={}
 for name,rec in oldseal['manifests'].items():
  b=read_safe(ROOT,'inputs/private/r6-'+name);require(record(b)==rec,'r6 copied manifest mismatch')
  for e in json.loads(b)['files']:old_entries[e['path']]={k:e[k] for k in ['size','sha256']}
 before=json.loads(read_safe(ROOT,'inputs/private/r6-before.json'))
 require(set(before)==set(old_entries)|CONTROL,'r6 before inventory mismatch')
 require(all(before[k]==v for k,v in old_entries.items()),'r6 before manifest linkage mismatch')
 require(snapshot(R6)==before,'frozen r6 differs from independent initial snapshot')
 for source,local in [('candidate.md','r6-candidate.md'),('source-contracts.md','r6-source-contracts.md'),('retrieval-upstream.json','r6-retrieval-upstream.json')]:
  require(record(read_safe(ROOT,'inputs/private/'+local))==old_entries[source],'r6 copied context mismatch')
 tree=json.loads(read_safe(ROOT,'inputs/private/context/preprints-tree.json'))
 require(not tree.get('truncated',False),'truncated source tree')
 require(record(read_safe(ROOT,'inputs/private/context/preprints-tree.json'))==old_entries['inputs/private/context/sources/preprints-tree.json'],'source tree r6 linkage mismatch')
 paths={e['path']:e for e in tree['tree']}
 rows=json.loads(read_safe(ROOT,'inputs/private/r6-retrieval-upstream.json'));require(len(rows)==5,'pin count mismatch')
 for e in rows:
  b=read_safe(ROOT,e['local']);require(record(b)=={k:e[k] for k in ['size','sha256']},'retrieval byte mismatch')
  blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  require(blob==e['git_blob']==paths[e['path']]['sha'],'pinned Git blob mismatch')
  require(e['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path'],'pinned URL mismatch')
 require(json.loads(read_safe(ROOT,'status.json'))['status']=='UNRESOLVED','live status mismatch')
 return counts,actual,before

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--seal-sha256',required=True);ap.add_argument('--authenticate-only',action='store_true');a=ap.parse_args()
 counts,own_before,old_before=authenticate(a.seal_sha256)
 print(f'AUTHENTICATED {counts[0]} inputs, {counts[1]} outputs; 5 pinned Git blobs; frozen r6 61 files; no checker executed before authentication',flush=True)
 if a.authenticate_only:return
 env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONHASHSEED']='0'
 try:
  for script,receipt in [('checks.py','checks-receipt.txt'),('exchange_probe.py','exchange-probe-receipt.txt')]:
   r=subprocess.run([sys.executable,'-I','-B',str(ROOT/script)],cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
   require(r.returncode==0 and not r.stderr,'read-only checker failed: '+script+' '+r.stderr.decode(errors='replace'))
   require(r.stdout==read_safe(ROOT,receipt),'immutable replay receipt mismatch: '+receipt)
   print('REPLAY '+script+' '+sha(r.stdout),flush=True)
 finally:
  # This code executes also if a checker rejects a rank or malformed fixture.
  require(snapshot(ROOT)==own_before,'round tree changed during replay')
  require(snapshot(R6)==old_before,'frozen r6 changed during replay')
  print('POSTCHECK: independently hashed both complete trees; byte-identical before/after, including all frozen inputs/outputs',flush=True)
 authenticate(a.seal_sha256)
 print('PASS_INTEGRITY_AND_EXACT_FINITE_DIAGNOSTICS_ONLY_H_UNRESOLVED')
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
