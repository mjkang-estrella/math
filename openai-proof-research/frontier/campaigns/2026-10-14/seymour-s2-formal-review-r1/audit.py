#!/usr/bin/env python3
"""Independent scoped S2 audit replay. Myeongjin Kang, MIT. No author writes."""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, sys
H=Path(__file__).resolve().parent
A=H.parent/'seymour-s2-formal-r1'
ANCHOR='dc95788a4e2d44c74c9c9a5d2a705641fc61baadc479cfe5903859911e01bc47'
LEAN=H.parents[4]/'dlp-research/.tools/lean-4.34.1-linux/bin/lean'
# parents[4] is the shared math workspace.
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
def authenticate():
 assert sha(A/'output-manifest.json')==ANCHOR
 manifest=json.loads((A/'output-manifest.json').read_text())
 listed={x['path'] for x in manifest['files']}
 assert len(listed)==len(manifest['files'])==40
 actual={str(p.relative_to(A)) for p in A.rglob('*') if p.is_file()}
 assert actual==listed|{'output-manifest.json'},(actual-listed,listed-actual)
 for e in manifest['files']:
  p=A/e['path'];assert not p.is_symlink() and p.resolve().is_relative_to(A)
  assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],e['path']
 inputs={}
 for e in json.loads((A/'input-manifest.json').read_text())['files']:
  p=H.parent/e['path_relative_to_campaign'];assert sha(p)==e['sha256'];inputs[e['path_relative_to_campaign']]=sha(p)
 return {'externally_supplied_manifest_sha256':ANCHOR,'exact_payload_members':40,'inputs':inputs}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',default='run');args=ap.parse_args()
 auth=authenticate();out=(H/args.output).resolve();assert out.is_relative_to(H) and out!=H
 out.mkdir(exist_ok=False);logs=out/'logs';logs.mkdir();build=out/'build';build.mkdir()
 dump(out/'authentication.json',auth)
 env=os.environ.copy();env['GIT_OPTIONAL_LOCKS']='0';env['PYTHONDONTWRITEBYTECODE']='1'
 libs=[];pins={};cache=H.parent/'formal/.lake/packages'
 for p in json.loads((A/'lake-manifest.json').read_text())['packages']:
  d=cache/p['name'];actual=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],env=env,text=True).strip();assert actual==p['rev']
  assert not subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],env=env,text=True)
  pins[p['name']]=actual
  lib=d/'.lake/build/lib/lean'
  if lib.is_dir():libs.append(str(lib.resolve()))
 env['LEAN_PATH']=os.pathsep.join([str(build)]+libs)
 receipt={'status':'RUNNING','authentication':auth,'pins':pins,'lean_sha256':sha(LEAN),'runs':[]}
 def run(label,cmd,cwd=build,expected=0):
  # Mount the entire external workspace/cache read-only; only this review may be written.
  cmd=['bwrap','--ro-bind','/','/','--bind',str(H),str(H),'--proc','/proc','--dev','/dev','--chdir',str(cwd),*map(str,cmd)]
  r=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=600)
  (logs/(label+'.stdout')).write_text(r.stdout);(logs/(label+'.stderr')).write_text(r.stderr)
  receipt['runs'].append({'label':label,'exit_code':r.returncode,'command':cmd,'stdout_sha256':hashlib.sha256(r.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(r.stderr.encode()).hexdigest()})
  dump(out/'receipt.json',receipt)
  assert r.returncode==expected,(label,r.stdout,r.stderr)
  if expected==0: assert not re.search(r'\b(?:error:|warning:|sorryAx|SOME FAIL|FAILED|Traceback)',r.stdout+r.stderr)
  print(label,'PASS',flush=True);return r
 v=run('version',[LEAN,'--version']);assert '4.34.1' in v.stdout and '5045d0056413266e57c625dcd7c365b10e377c52' in v.stdout
 for f in ['SeymourSupport.lean','Controls.lean','Checks.lean','ControlChecks.lean']:shutil.copyfile(A/f,build/f)
 run('support',[LEAN,'-o','SeymourSupport.olean','SeymourSupport.lean'])
 run('controls',[LEAN,'-o','Controls.olean','Controls.lean'])
 names={}
 for ns,f in [('SeymourSupport','SeymourSupport.lean'),('SeymourControls','Controls.lean')]:
  body=(build/f).read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',body)
  names[ns]=re.findall(r'^theorem (\w+)',body,re.M)
 assert len(names['SeymourSupport'])==11 and len(names['SeymourControls'])==7
 query='import Controls\nset_option pp.universes true\nset_option pp.explicit true\n'
 for ns,nsnames in names.items():
  for n in nsnames:query+=f'#check @{ns}.{n}\n#print axioms {ns}.{n}\n'
 (build/'AuditQueries.lean').write_text(query)
 r=run('independent-types-axioms',[LEAN,'AuditQueries.lean']);axioms={}
 for ns,nsnames in names.items():
  for n in nsnames:
   key=f'{ns}.{n}';m=re.search("'"+re.escape(key)+"' depends on axioms: \\[([^\\]]*)\\]",r.stdout)
   assert m,key
   ax=set(re.sub(r'\.\{[^}]*\}','',m[1]).split(', '));assert ax <= {'propext','Classical.choice','Quot.sound'},(key,ax)
   axioms[key]=sorted(ax)
 receipt['axioms']=axioms
 for label,f,prior in [('author-types','Checks.lean','types-axioms'),('author-control-types','ControlChecks.lean','example-types-axioms')]:
  r=run(label,[LEAN,f]);assert r.stdout==(A/'logs/first-build'/f'{prior}.stdout').read_text()
 run('author-semantic-checks',[sys.executable,'-B',A/'semantic_checks.py'])
 run('author-identity-check',[sys.executable,'-B',A/'verify.py'])
 # Exercise the actual runner, including zero exit diagnostics on both streams.
 for label,program,code in [('zero-fail',"print('SOME FAIL')",1),('zero-stderr',"import sys; print('error: injected',file=sys.stderr)",1),('exit-only','raise SystemExit(7)',1),('clean',"print('OK')",0)]:
  run('runner-'+label,[sys.executable,'-B',A/'checked_run.py','--log-prefix',logs/('inner-'+label),'--',sys.executable,'-c',program],expected=code)
 # Independent retained mutation sources, each truncation is separately compiled unmutated.
 source=(A/'SeymourSupport.lean').read_text()
 cases=[('boundary','boundary_indicators','(haq : a ≤ q)','(haq : a ≤ q + 1)'),('anchors','aggregate_negative','m - 1 ≤ (S.card : ℤ)','m - 2 ≤ (S.card : ℤ)'),('threshold','fiber_cardinality_strict','(hm : m = n^2 + 2)','(hm : m = n^2 + 1)'),('pruning','complement_pruning_contradiction','(hGain : M + 2*d < R.card + C.card)','(hGain : M + 2*d ≤ R.card + C.card)')]
 mutants=out/'mutants';mutants.mkdir()
 for label,nxt,old,new in cases:
  end=source.rfind('/--',0,source.index('theorem '+nxt));prefix=source[:end]+'end SeymourSupport\n';assert prefix.count(old)==1
  base=mutants/(label+'-baseline.lean');mut=mutants/(label+'-false.lean');base.write_text(prefix);mut.write_text(prefix.replace(old,new))
  run('baseline-'+label,[LEAN,base]);r=run('false-'+label,[LEAN,mut],expected=1)
  s=r.stdout+r.stderr;assert re.search('omega could not prove|unsolved goals|linarith failed',s)
  assert not re.search('unknown module|unexpected token|Unknown identifier|Type mismatch|Application type mismatch',s)
 # True finite-set and arbitrary-n witnesses written by this reviewer.
 shutil.copyfile(H/'ReviewControls.lean',build/'ReviewControls.lean')
 run('review-controls',[LEAN,'-o','ReviewControls.olean','ReviewControls.lean'])
 # Portable Lake project uses byte-identical config and source, pinned provisioned cache.
 portable=out/'portable';portable.mkdir();(portable/'.lake').mkdir()
 for f in ['lean-toolchain','lakefile.toml','lake-manifest.json','SeymourSupport.lean','Controls.lean','Checks.lean','ControlChecks.lean']:shutil.copyfile(A/f,portable/f)
 (portable/'.lake/packages').symlink_to(cache.resolve(),target_is_directory=True)
 # --no-build is not used: all four project libraries build from fresh sources.
 oldpath=env['PATH'];env['PATH']=str(LEAN.parent)+os.pathsep+oldpath
 run('lake-build',[LEAN.parent/'lake','build'],cwd=portable)
 assert sha(portable/'lake-manifest.json')==sha(A/'lake-manifest.json')
 assert all((portable/'.lake/build/lib/lean'/f'{n}.olean').is_file() for n in ['SeymourSupport','Controls','Checks','ControlChecks'])
 receipt.update(status='PASS_SCOPED_FORMAL_BUILD',full_graph_theorem_formalized=False,author_unchanged=authenticate()==auth,source_sha256={f:sha(A/f) for f in ['SeymourSupport.lean','Controls.lean','coverage.json']},read_only_external_mount=True)
 dump(out/'receipt.json',receipt)
if __name__=='__main__':main()
