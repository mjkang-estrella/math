#!/usr/bin/env python3
"""Replay frozen theorem against explicit external, already-built pinned dependencies."""
import argparse,hashlib,json,os,pathlib,re,subprocess,time
if hasattr(os, 'sched_getaffinity'):
 os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
p=argparse.ArgumentParser();p.add_argument('--dependency-root',type=pathlib.Path,default=os.environ.get('MAJORITY_DEPENDENCY_ROOT'));p.add_argument('--lean',default=os.environ.get('MAJORITY_LEAN','lean'));p.add_argument('--output',type=pathlib.Path,default=pathlib.Path('replay-output'));p.add_argument('--leanchecker',default=os.environ.get('MAJORITY_LEANCHECKER'));a=p.parse_args()
root=pathlib.Path(__file__).resolve().parent
if a.dependency_root is None:p.error('set --dependency-root or MAJORITY_DEPENDENCY_ROOT to the pinned .lake/packages directory')
deps=a.dependency_root.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
expected='751ac866bed61eb765969f5ea08e53c582f79431400786e418cfd1278e07d850'
source=root/'Majority.lean';assert hashlib.sha256(source.read_bytes()).hexdigest()==expected,'source hash mismatch'
version=subprocess.check_output([a.lean,'--version'],text=True);assert 'version 4.34.1,' in version,version
manifest=json.loads((root/'lake-manifest.json').read_text());paths=[];checks=[]
# Read revision metadata only. No git command or dependency mutation.
for pkg in manifest['packages']:
 d=deps/pkg['name'];meta=d/'.git'
 if meta.is_file():meta=(d/meta.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(meta/'HEAD').read_text().strip()
 if head.startswith('ref: '):
  ref=head[5:];rf=meta/ref
  if rf.exists():head=rf.read_text().strip()
  else:
   refs=(meta/'packed-refs').read_text().splitlines();head=next(x.split()[0] for x in refs if x.endswith(' '+ref))
 assert head==pkg['rev'],(pkg['name'],head,pkg['rev'])
 lib=d/'.lake/build/lib/lean'
 if pkg['name']=='mathlib':assert lib.is_dir(),str(lib)
 if lib.is_dir():paths.append(str(lib))
 checks.append({'name':pkg['name'],'rev':head,'library':str(lib),'prebuilt_library_present':lib.is_dir()})
# Clear inherited LEAN_PATH and other Lean settings; preserve only basic runtime environment.
env={k:v for k,v in os.environ.items() if k in ['PATH','HOME','TMPDIR','LD_LIBRARY_PATH']};env['LEAN_PATH']=os.pathsep.join(paths+[str(out)]);env['OMP_NUM_THREADS']='2'
env['PATH']=str(pathlib.Path(__import__('shutil').which(a.lean) or a.lean).resolve().parent)+os.pathsep+env.get('PATH','/usr/bin:/bin')
import shutil
shutil.copyfile(source,out/source.name)
cmd=[a.lean,'-j2','-DwarningAsError=true','-o','Majority.olean',source.name]
t=time.monotonic();r=subprocess.run(cmd,cwd=out,env=env,text=True,capture_output=True);elapsed=time.monotonic()-t
(out/'lean.stdout.log').write_text(r.stdout);(out/'lean.stderr.log').write_text(r.stderr)
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",r.stdout)
allowed={'propext','Classical.choice','Quot.sound'}
valid=len(axioms)==4 and all(set(x.strip() for x in names.split(','))<=allowed for _,names in axioms)
result={'exit_code':r.returncode,'elapsed_seconds':elapsed,'command':cmd,'source_sha256':expected,'lean_version':version.strip(),'external_prebuilt_dependencies':checks,'axioms':axioms,'axiom_audit_pass':valid,'build_from_network_source':False,'max_lean_threads':2,'leanchecker':'not requested'}
if a.leanchecker and r.returncode==0:
 c=subprocess.run([a.leanchecker,'Majority'],cwd=out,env=env,text=True,capture_output=True);(out/'leanchecker.log').write_text(c.stdout+c.stderr);result['leanchecker']={'exit_code':c.returncode}
(out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
assert r.returncode==0 and valid and (not a.leanchecker or result['leanchecker']['exit_code']==0),'strict Lean replay or axiom audit failed'
