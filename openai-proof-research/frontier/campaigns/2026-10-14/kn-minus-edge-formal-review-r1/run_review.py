#!/usr/bin/env python3
"""Independent review build driver. Copyright 2026 Myeongjin Kang; MIT."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys, time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
AUTHOR=HERE.parent/'kn-minus-edge-formal-v1'
CACHE=HERE.parent/'formal/.lake/packages'
LEAN=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
def record(p):
    b=p.read_bytes(); return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def run(label,cmd,cwd,env):
    start=time.monotonic(); p=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True)
    (HERE/'logs'/f'{label}.stdout').write_text(p.stdout); (HERE/'logs'/f'{label}.stderr').write_text(p.stderr)
    row={'label':label,'command':list(map(str,cmd)),'cwd':str(cwd),'exit_code':p.returncode,'seconds':time.monotonic()-start}
    results['runs'].append(row); (HERE/'build-receipt.json').write_text(json.dumps(results,indent=2)+'\n')
    print(label,p.returncode,flush=True)
    if p.returncode: raise RuntimeError(label)
    return p.stdout
results={'scope':'independent scoped formal support audit; no full theorem certification','runs':[],'source_files':[],'dependencies':[]}
env=os.environ.copy(); env['GIT_OPTIONAL_LOCKS']='0'; env['PYTHONDONTWRITEBYTECODE']='1'
build=HERE/'build'
build.mkdir(exist_ok=True)
libs=[]
for pkg in json.loads((AUTHOR/'lake-manifest.json').read_text())['packages']:
    p=CACHE/pkg['name']; rev=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True,env=env).strip()
    assert rev==pkg['rev'],(pkg['name'],rev)
    dirty=subprocess.check_output(['git','-C',str(p),'status','--porcelain','--untracked-files=no'],text=True,env=env)
    assert not dirty,(pkg['name'],dirty)
    results['dependencies'].append({'name':pkg['name'],'revision':rev,'tracked_tree_clean':True})
    lib=p/'.lake/build/lib/lean'
    if lib.is_dir(): libs.append(str(lib.resolve()))
results['compiler']=record(LEAN); results['compiler_realpath']=str(LEAN.resolve())
version=run('compiler-version',[str(LEAN),'--version'],build,env)
assert '4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version
for f in ['KnMinusEdge.lean','Controls.lean','Checks.lean','ControlChecks.lean']:
    results['source_files'].append(record(AUTHOR/f)); shutil.copyfile(AUTHOR/f,build/f)
env['LEAN_PATH']=os.pathsep.join([str(build)]+libs)
results['LEAN_PATH']=env['LEAN_PATH']
for label,args in [('fresh-core',['-o','KnMinusEdge.olean','KnMinusEdge.lean']),('fresh-author-controls',['-o','Controls.olean','Controls.lean']),('author-types-axioms',['Checks.lean']),('author-control-types-axioms',['ControlChecks.lean'])]:
    run(label,[str(LEAN),*args],build,env)
# Queries generated independently from every source declaration; inspect exact types and full definitions.
queries=['import KnMinusEdge','import Controls','set_option pp.universes true','set_option pp.explicit true']
names=[]
for f,ns in [('KnMinusEdge.lean','KnMinusEdge'),('Controls.lean','KnMinusEdgeControls')]:
    source=(build/f).read_text()
    assert not re.search(r'\b(sorry|admit|unsafe|native_decide)\b|^\s*axiom\b',source,re.M)
    for name in re.findall(r'^(?:@\[simp\] )?(?:noncomputable )?(?:def|theorem) (\w+)',source,re.M):
        full=ns+'.'+name; names.append(full); queries += ['#check @'+full,'#print axioms '+full]
(build/'IndependentQueries.lean').write_text('\n'.join(queries)+'\n')
q=run('independent-types-axioms',[str(LEAN),'IndependentQueries.lean'],build,env)
reports={}
for name in names:
    m=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",q)
    if m:
        ax=set(re.sub(r'\.\{[^}]*\}','',m[1]).replace('\n',' ').replace(' ','').split(','))
    else:
        assert f"'{name}' does not depend on any axioms" in q,name; ax=set()
    assert ax <= {'propext','Classical.choice','Quot.sound'},(name,ax)
    reports[name]=sorted(ax)
results['axiom_reports']=reports
results['status']='PASS fresh author source and all 73 declaration axiom queries'
(HERE/'build-receipt.json').write_text(json.dumps(results,indent=2)+'\n')
print(results['status'],flush=True)
