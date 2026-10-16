#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Rebuild original scoped support and review controls in a disposable directory.

Verify the enclosing bundle first. Uses explicit local compiler/dependency cache;
never downloads, modifies frozen sources, or reuses support .olean files.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from bundle_common import check, parse, read, require, sha

PREFIX='frontier/campaigns/2026-10-14/'
COMPILER='5045d0056413266e57c625dcd7c365b10e377c52'


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    p.add_argument('--lean',type=Path,required=True)
    p.add_argument('--cache',type=Path,required=True)
    p.add_argument('--check-setup',action='store_true')
    a=p.parse_args();root=a.root.resolve();lean=a.lean.resolve();cache=a.cache.resolve()
    author=root/PREFIX/'kn-minus-edge-formal-v1';review=root/PREFIX/'kn-minus-edge-formal-review-r1'
    for folder in [author,review]:
        for row in parse(read(folder,'output-manifest.json'))['files']:check(read(folder,row['path']),row)
    version=subprocess.check_output([str(lean),'--version'],text=True)
    require('4.34.1' in version and COMPILER in version,'compiler version/commit mismatch')
    lock=parse(read(author,'lake-manifest.json'));libs=[];pins={}
    env=os.environ.copy();env['GIT_OPTIONAL_LOCKS']='0';env['PYTHONDONTWRITEBYTECODE']='1'
    for pkg in lock['packages']:
        base=cache/pkg['name']
        rev=subprocess.check_output(['git','-C',str(base),'rev-parse','HEAD'],text=True,env=env).strip()
        require(rev==pkg['rev'],'dependency revision mismatch: '+pkg['name'])
        require(not subprocess.check_output(['git','-C',str(base),'status','--porcelain','--untracked-files=no'],env=env),'modified dependency: '+pkg['name'])
        pins[pkg['name']]=rev;lib=base/'.lake/build/lib/lean'
        if lib.is_dir():libs.append(str(lib))
    require(pins['mathlib']=='d13f23b723b8a846827a245b89c10fc7d3f11612','mathlib pin mismatch')
    report=dict(status='SETUP_PASS',compiler=version.strip(),dependency_revisions=pins,full_crossing_certificate=False,runs=[])
    if not a.check_setup:
        with tempfile.TemporaryDirectory(prefix='kn-release-lean-') as temp:
            build=Path(temp)
            for name in ['KnMinusEdge.lean','Controls.lean','Checks.lean','ControlChecks.lean','ReviewControls.lean','ReviewQueries.lean','ReadableQueries.lean']:
                (build/name).write_bytes(read(review,'build/'+name))
            env['LEAN_PATH']=os.pathsep.join([str(build),*libs])
            stages=[('fresh-core',['-o','KnMinusEdge.olean','KnMinusEdge.lean'],'fresh-core'),
                    ('fresh-author-controls',['-o','Controls.olean','Controls.lean'],'fresh-author-controls'),
                    ('review-controls',['-o','ReviewControls.olean','ReviewControls.lean'],'review-controls'),
                    ('author-types-axioms',['Checks.lean'],'author-types-axioms'),
                    ('author-control-types-axioms',['ControlChecks.lean'],'author-control-types-axioms'),
                    ('review-control-types-axioms',['ReviewQueries.lean'],'review-control-types-axioms'),
                    ('readable-types-axioms',['ReadableQueries.lean'],'readable-types-axioms')]
            for label,args,expected in stages:
                run=subprocess.run([str(lean),*args],cwd=build,env=env,capture_output=True)
                require(run.returncode==0 and not run.stderr,
                        'Lean stage failed: '+label+' '+run.stdout.decode(errors='replace')+run.stderr.decode(errors='replace'))
                if expected:require(run.stdout==read(review,'logs/'+expected+'.stdout'),'type/axiom output mismatch: '+label)
                report['runs'].append(dict(stage=label,returncode=run.returncode,stdout_sha256=sha(run.stdout),matches_frozen_output=bool(expected)))
                print(label+' PASS',file=sys.stderr,flush=True)
            for name in ['semantic_checks.py','checked_run.py']:(build/name).write_bytes(read(author,name))
            run=subprocess.run([sys.executable,'-B','semantic_checks.py'],cwd=build,env=env,capture_output=True)
            require(run.returncode==0 and not run.stderr,'semantic arithmetic failed')
            report['arithmetic_stdout']=run.stdout.decode()
            report['status']='PASS_FRESH_SCOPED_BUILD'
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    try:main()
    except (OSError,ValueError,KeyError,TypeError,subprocess.CalledProcessError) as exc:
        sys.exit('FORMAL REPRODUCTION FAILED: '+str(exc))
