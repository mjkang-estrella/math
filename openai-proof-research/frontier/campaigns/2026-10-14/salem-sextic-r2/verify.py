#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright 2026 Myeongjin Kang
"""Read-only, fail-closed authentication. Never regenerates a fixture.
No research/numerical code is loaded before all authentication checks pass.
"""
import argparse,hashlib,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[3]
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PRIOR='abeda4f3244350e97fbdd5cafffa6e96db4b4efa0f423660b80a0662ed144bfb'
SCOPE='143778fc32d5eb1f668b4b941ad1bd184b19c71b1bfb2792bee78b1effdd2bdd'
class Failure(Exception):pass
def demand(ok,msg):
 if not ok:raise Failure(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(base,rel):
 p=Path(rel)
 demand(not p.is_absolute() and '..' not in p.parts and str(p)==rel,'unsafe record path')
 target=base/p
 demand(target.is_relative_to(base),'outside package')
 return target
def check_record(base,r):
 p=safe(base,r['path']);demand(p.is_file() and not p.is_symlink(),'missing/symlink: '+r['path'])
 demand(p.stat().st_size==r['size'] and digest(p)==r['sha256'],'size/hash mismatch: '+r['path'])
 return p
def inventory(base,expected):
 actual=set();dirs=set()
 for p in base.rglob('*'):
  demand(not p.is_symlink(),'symlink member: '+str(p))
  rel=str(p.relative_to(base))
  if p.is_file():actual.add(rel)
  elif p.is_dir():dirs.add(rel)
  else:raise Failure('nonregular member: '+rel)
 demand(actual==set(expected),'exact file membership mismatch: '+str(base))
 implied={str(a) for f in expected for a in Path(f).parents if str(a)!='.'}
 demand(dirs==implied,'exact directory membership mismatch: '+str(base))
 return sorted(actual)
def readj(p):return json.loads(p.read_text())
def authenticate(anchor,required):
 # External anchor gate FIRST, before reading any manifest or source fixture.
 demand(anchor==digest(HERE/'seal.json'),'external anchor mismatch')
 demand(sys.flags.optimize==0,'optimized Python is not accepted')
 seal=readj(HERE/'seal.json')
 demand(seal['mathematical_status']==required,'required mathematical status mismatch')
 demand(seal['mathematical_status']=='UNRESOLVED' and seal['counted'] is False,'unsupported status/count')
 demand(seal['upstream_commit']==PIN and seal['scope_sha256']==SCOPE,'pin/scope metadata mismatch')
 demand((HERE/'seal.sha256').read_text()==anchor+'  seal.json\n','detached seal text mismatch')
 for r in seal['manifests']:check_record(HERE,r)
 manifests=[readj(HERE/x) for x in ['inputs-manifest.json','outputs-manifest.json']]
 expected=[]
 for m in manifests:
  for r in m['files']:check_record(HERE,r);expected.append(r['path'])
 demand(len(expected)==len(set(expected)),'duplicate/overlapping manifest entries')
 expected+=['inputs-manifest.json','outputs-manifest.json','seal.json','seal.sha256']
 own=inventory(HERE,expected)
 demand(digest(HERE/'original-scope.md')==SCOPE,'frozen scope mismatch')
 status=readj(HERE/'status.json');demand(status['mathematical_status']=='UNRESOLVED' and status['counted'] is False,'status mismatch')
 fixture=readj(HERE/'inputs/context/prior-package-fixture.json')
 demand(fixture['external_anchor']==PRIOR,'wrong prior anchor fixture')
 prior=safe(PROJECT,fixture['root'])
 demand(digest(prior/'seal.json')==PRIOR,'prior external anchor mismatch')
 ps=readj(prior/'seal.json')
 bound=set()
 for key in ['inputs','outputs','receipt']:
  r=ps[key];check_record(prior,r);bound.add(r['path'])
 for name in ['inputs-manifest.json','outputs-manifest.json']:
  for r in readj(prior/name)['files']:check_record(prior,r);bound.add(r['path'])
 bound.update(['seal.json','seal.sha256'])
 demand((prior/'seal.sha256').read_text()==PRIOR+'  seal.json\n','prior detached text mismatch')
 prior_members=inventory(prior,bound)
 demand(len(prior_members)==27,'prior member count changed')
 fixture_members=set()
 for r in fixture['files']:
  p=check_record(PROJECT,r);fixture_members.add(str(p.relative_to(prior)))
 demand(fixture_members==set(prior_members),'prior fixture membership mismatch')
 ids=readj(HERE/'source-identities.json');demand(ids['commit']==PIN,'source commit mismatch')
 for r in ids['blobs']:
  p=safe(PROJECT,r['external_path']);data=p.read_bytes()
  demand(p.is_relative_to(prior) and str(p.relative_to(prior)) in bound,'unbound source')
  demand(len(data)==r['size'] and hashlib.sha256(data).hexdigest()==r['sha256'],'source size/hash mismatch')
  demand(hashlib.sha1(b'blob %d\0'%len(data)+data).hexdigest()==r['git_blob_sha1'],'source Git blob mismatch')
 receipt=readj(HERE/'evidence/unchanged-input-receipt.json')
 demand(receipt['external_unchanged'] and receipt['scope_unchanged'],'unchanged-input receipt mismatch')
 for r in receipt['input_files']:check_record(HERE,r)
 protected=[HERE/x for x in own]+[prior/x for x in prior_members]
 return protected,{'own_files':len(own),'prior_files':len(prior_members),'pinned_blobs':len(ids['blobs'])}
def guard(event,args):
 if event=='open':
  _,mode,flags=args
  if (isinstance(mode,str) and any(x in mode for x in ['w','a','x','+'])) or (isinstance(flags,int) and flags&(1|2|64|512|1024)):
   raise PermissionError('verification denies writes')
 if event.startswith(('socket.','subprocess.','ctypes.')) or event in {
  'os.system','os.exec','os.posix_spawn','os.spawn','os.remove','os.unlink','os.rename',
  'os.rmdir','os.mkdir','os.link','os.symlink','os.chmod','os.chown','os.utime','os.truncate'}:
  raise PermissionError('verification denies side effects: '+event)
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--anchor',required=True)
 parser.add_argument('--require-math',default='UNRESOLVED');parser.add_argument('--exact',action='store_true');args=parser.parse_args()
 try:
  protected,counts=authenticate(args.anchor,args.require_math)
  before={str(p):digest(p) for p in protected}
  ran=False
  if args.exact:
   # This is the FIRST research-code import/execution, after the entire gate.
   import runpy
   sys.addaudithook(guard)
   ns=runpy.run_path(str(HERE/'scripts/exact_check.py'),run_name='authenticated_exact_diagnostic')
   got=ns['check']();want=readj(HERE/'evidence/exact-check.json')
   demand(json.dumps(got,sort_keys=True)==json.dumps(want,sort_keys=True),'exact diagnostic replay differs')
   ran=True
  demand(before=={str(p):digest(p) for p in protected},'protected tree changed during verification')
  print(json.dumps({'status':'AUTHENTICATED_ARTIFACTS_ONLY','mathematics':'UNRESOLVED','counted':False,**counts,'exact_diagnostic_reproduced':ran,'discovery_or_legacy_code_executed':False,'protected_files_unchanged':True,'writes':False},sort_keys=True))
  return 0
 except Exception as e:
  print(json.dumps({'status':'REJECTED','reason':str(e),'writes':False},sort_keys=True));return 2
if __name__=='__main__':sys.exit(main())
