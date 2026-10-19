#!/usr/bin/env python3
"""Copied integrity controls; writes only disposable copies under --root.
The authenticated original verifier is run against each copy. Original code MIT.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

def snapshot(root):
    files, dirs = {}, []
    for p in root.rglob('*'):
        r=p.relative_to(root).as_posix()
        if p.is_dir(): dirs.append(r)
        elif p.is_file(): files[r]=hashlib.sha256(p.read_bytes()).hexdigest()
        else: raise RuntimeError('nonregular original root')
    return {'files':files,'directories':sorted(dirs)}

def run():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--expected-final',required=True);ap.add_argument('--expected-report',required=True);a=ap.parse_args()
    root=a.root.resolve();before=snapshot(root);workspace=root/'control-work';assert not workspace.exists();workspace.mkdir()
    verifier=root/'packet/public/verify.py';results=[]
    cases=['baseline','payload-edit','payload-delete','extra-file','extra-directory','extra-hidden','symlink-file','symlink-directory','fifo','manifest-edit','FINAL-edit','wrong-final-argument','report-edit','wrong-report-argument','freeze-edit','canonical-edit','primary-edit','history-edit','outer-freeze-edit']
    try:
        for name in cases:
            copy=workspace/'copy';copy.mkdir();shutil.copytree(root/'packet',copy/'packet')
            for n in ['FINAL','REPORT.md','freeze-anchor.json']:shutil.copyfile(root/n,copy/n)
            q=copy/'packet';final=a.expected_final;report=a.expected_report
            def append(p): p.write_bytes(p.read_bytes()+b'\nCONTROL MUTATION\n')
            if name=='payload-edit':append(q/'public/proof.md')
            elif name=='payload-delete':(q/'public/proof.md').unlink()
            elif name=='extra-file':(q/'EXTRA').write_text('x')
            elif name=='extra-directory':(q/'extra-empty').mkdir()
            elif name=='extra-hidden':(q/'.unexpected').write_text('x')
            elif name=='symlink-file':(q/'public/proof.md').unlink();(q/'public/proof.md').symlink_to(root/'packet/public/proof.md')
            elif name=='symlink-directory':(q/'extra-link').symlink_to(root/'packet/public',target_is_directory=True)
            elif name=='fifo':os.mkfifo(q/'unexpected-fifo')
            elif name=='manifest-edit':append(q/'MANIFEST.json')
            elif name=='FINAL-edit':(copy/'FINAL').write_text('0'*64+'\n')
            elif name=='wrong-final-argument':final='0'*64
            elif name=='report-edit':append(copy/'REPORT.md')
            elif name=='wrong-report-argument':report='0'*64
            elif name=='freeze-edit':append(q/'public/FROZEN.md')
            elif name=='canonical-edit':append(q/'private/upstream/register.json')
            elif name=='primary-edit':append(next((q/'private/primary').glob('*.pdf')))
            elif name=='history-edit':append(q/'private/history/register.json')
            elif name=='outer-freeze-edit':append(copy/'freeze-anchor.json')
            cmd=[sys.executable,'-B',str(verifier),'--root',str(copy),'--expected-final',final,'--expected-report',report]
            r=subprocess.run(cmd,capture_output=True,text=True,timeout=30)
            expected=0 if name=='baseline' else 1
            results.append({'case':name,'expected_exit':expected,'actual_exit':r.returncode,'matched':r.returncode==expected,'output':r.stdout.strip() or r.stderr.strip()})
            shutil.rmtree(copy)
    finally:
        shutil.rmtree(workspace)
    after=snapshot(root)
    result={'controls':results,'all_expected':all(x['matched'] for x in results),'whole_original_root_restored_unchanged':before==after,'original_files':len(before['files']),'original_directories':len(before['directories']),'mathematical_gate':False,'detached_final':a.expected_final,'outside_report':a.expected_report}
    print(json.dumps(result,indent=2))
    if not result['all_expected'] or before!=after:sys.exit(1)
if __name__=='__main__':run()
