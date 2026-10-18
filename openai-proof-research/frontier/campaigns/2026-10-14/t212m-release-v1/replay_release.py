#!/usr/bin/env python3
"""Authenticate an extracted T212M selection, then replay one scoped build. MIT."""
import argparse
import os
from pathlib import Path
import subprocess
import sys
from final_release import verify
from release_common import *
HERE=Path(__file__).absolute().parent

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=['pdf','original','independent'])
    p.add_argument('--manifest-anchor',required=True)
    p.add_argument('--implementation-anchor',required=True)
    p.add_argument('--final',action='store_true')
    p.add_argument('--r2-anchor');p.add_argument('--closure-anchor')
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--lean',type=Path);p.add_argument('--cache',type=Path)
    p.add_argument('--tectonic',type=Path)
    a=p.parse_args()
    data,ds=tree(HERE)
    verify(data,ds,a.manifest_anchor,a.implementation_anchor,a.final,a.r2_anchor,a.closure_anchor)
    inputs=[HERE]
    if a.mode=='pdf':
        require(a.tectonic is not None,'absolute tectonic path required')
        read(a.tectonic.parent,a.tectonic.name);inputs.append(a.tectonic)
        argv=[str(HERE/'t212m-manuscript-v1/build.py'),'--tectonic',str(a.tectonic)]
    else:
        require(a.lean is not None and a.cache is not None,'absolute Lean/cache paths required')
        read(a.lean.parent,a.lean.name);ancestry(a.cache)
        require(stat.S_ISDIR(a.cache.lstat().st_mode),'unsafe cache root')
        inputs += [a.lean,a.cache]
        if a.mode=='original':
            argv=[str(HERE/'t212m-formal-v1/rebuild.py')]
        else:
            selection=parse(data['public-selection-final-draft.json'])
            argv=[str(HERE/'reproduce_supplement.py'),'--formal',str(HERE/'t212m-formal-v1'),
                  '--review',str(HERE/'t212m-formal-review-r1'),
                  '--formal-anchor',selection['anchors']['t212m-formal-v1']['sha256'],
                  '--review-anchor',selection['anchors']['t212m-formal-review-r1']['sha256']]
        argv += ['--lean',str(a.lean),'--cache',str(a.cache)]
    new_output(a.output,inputs)
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    subprocess.run([sys.executable,'-B',*argv,'--output',str(a.output)],env=env,check=True)
    after,after_dirs=tree(HERE)
    require(after==data and after_dirs==ds,'selected input changed during replay')
    print('PASS_SCOPED_'+a.mode.upper()+'_REPLAY; not full stochastic formalization or acceptance')
if __name__=='__main__':
    try:main()
    except (ValueError,OSError,KeyError,TypeError,subprocess.CalledProcessError) as e:
        print('REFUSED: '+str(e),file=sys.stderr);sys.exit(1)
