#!/usr/bin/env python3
"""Independent fresh-source audit; writes only inside this review. MIT, Myeongjin Kang 2026."""
import argparse, hashlib, json, os, re, subprocess, tempfile, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
LEAN=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
CACHE=HERE.parent/'formal/.lake/packages'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def digest(b): return hashlib.sha256(b).hexdigest()
def main():
 parser=argparse.ArgumentParser(); parser.add_argument('--controls-only',action='store_true'); args=parser.parse_args()
 lock=json.loads((HERE/'author-copy/lake-manifest.json').read_text()); libs=[]; revs={}
 for p in lock['packages']:
  path=CACHE/p['name']; rev=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
  assert rev==p['rev']; revs[p['name']]=rev
  lib=path/'.lake/build/lib/lean'
  if lib.is_dir(): libs.append(str(lib.resolve()))
 version=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
 assert '4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version
 source=(HERE/'author-copy/StaircaseSupport.lean').read_bytes()
 assert digest(source)=='a8a8473d98a673790eb8e72546b890aa93bfba02351a97f401c39d4dbc10e989'
 support=(HERE/'ReviewSupport.lean').read_text()
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', support)
 names=re.findall(r'^(?:def|theorem|abbrev) (\w+)',support,re.M)
 checks='import ReviewSupport\nset_option pp.universes true\n'+''.join(f'#check @StaircaseReview.{n}\n#print axioms StaircaseReview.{n}\n' for n in names)
 (HERE/'ReviewChecks.lean').write_text(checks)
 runs=[]; started=time.time()
 def run(label,cmd,cwd,env,success=True,count=0):
  t=time.time(); p=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True,timeout=300)
  log=p.stdout+p.stderr; (HERE/'logs'/f'{label}.log').write_text(log)
  rows=re.findall(r'depends on axioms: \[([^\]]*)\]',log)
  reports=len(rows)+len(re.findall(r'does not depend on any axioms',log))
  axioms=set().union(*(set(re.sub(r'\.\{[^}]*\}','',row).split(', '))-{''} for row in rows)) if rows else set()
  ok=(p.returncode==0 and not any(s in log for s in ['warning:','sorryAx','error:']) and reports==count and axioms<=ALLOWED) if success else (p.returncode!=0 and 'error:' in log and 'unsolved goals' in log and 'sorryAx' not in log)
  runs.append({'label':label,'command':cmd,'cwd':'fresh disposable directory inside review','exit_code':p.returncode,'seconds':round(time.time()-t,3),'expected':'success' if success else 'semantic proof rejection','axiom_reports':reports,'axioms':sorted(axioms),'log_sha256':digest(log.encode()),'passed':ok})
  print(label, 'PASS' if ok else 'FAIL', flush=True)
  if not ok:
   print(log,flush=True); (HERE/'attempt.json').write_text(json.dumps(runs,indent=2)+'\n'); raise SystemExit(1)
 with tempfile.TemporaryDirectory(prefix='.independent-build-',dir=HERE) as d:
  temp=Path(d); env=os.environ.copy(); env['LEAN_PATH']=os.pathsep.join([d]+libs)
  (temp/'StaircaseSupport.lean').write_bytes(source)
  run('fresh-source',[str(LEAN),'-o','StaircaseSupport.olean','StaircaseSupport.lean'],temp,env)
  fresh=digest((temp/'StaircaseSupport.olean').read_bytes())
  for name in ['Checks.lean','Controls.lean']:
   (temp/name).write_bytes((HERE/'author-copy'/name).read_bytes())
  if not args.controls_only:
   run('author-types',[str(LEAN),'Checks.lean'],temp,env,count=20)
   run('author-controls',[str(LEAN),'Controls.lean'],temp,env,count=6)
  for name in ['ReviewSupport.lean','ReviewChecks.lean']:
   (temp/name).write_bytes((HERE/name).read_bytes())
  run('review-controls',[str(LEAN),'-o','ReviewSupport.olean','ReviewSupport.lean'],temp,env)
  run('review-types',[str(LEAN),'ReviewChecks.lean'],temp,env,count=len(names))
 if not args.controls_only:
  mutations=[('missing-inverse',source.decode().replace('θ (ρ g⁻¹ x)','θ (ρ g x)')),
    ('right-coordinate-shift',source.decode().replace('a (h⁻¹ * g)','a (g * h⁻¹)')),
    ('zero-normalization',source.decode().replace('if g = 1 then 1 else 0','if g = 1 then 0 else 0'))]
  for name,text in mutations:
   assert text.encode()!=source
   dest=HERE/'mutations'; dest.mkdir(exist_ok=True); (dest/(name+'.lean')).write_text(text)
   with tempfile.TemporaryDirectory(prefix='.mutation-',dir=HERE) as d:
    temp=Path(d); (temp/'StaircaseSupport.lean').write_text(text); env=os.environ.copy(); env['LEAN_PATH']=os.pathsep.join([d]+libs)
    run('mutation-'+name,[str(LEAN),'-o','StaircaseSupport.olean','StaircaseSupport.lean'],temp,env,success=False)
 result={'status':'PASS' if not args.controls_only else 'PASS controls only; incomplete audit','lean_version':version,'compiler_sha256':digest(LEAN.read_bytes()),'dependency_revisions':revs,'cache':str(CACHE),'fresh_source_sha256':digest(source),'fresh_olean_sha256':fresh,'review_source_sha256':digest(support.encode()),'review_declarations':names,'runs':runs,'total_seconds':round(time.time()-started,3),'trusted_setup':'Exact local compiler and existing shared dependency oleans; dependencies not rebuilt or kernel-rechecked recursively. Git HEAD pins do not attest cached olean content. No existing support olean used. No network or dependency/cache mutations.'}
 (HERE/('audit-receipt.json' if not args.controls_only else 'controls-attempt.json')).write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__': main()
