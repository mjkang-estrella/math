#!/usr/bin/env python3
# Copyright2026 Myeongjin Kang. MIT.
"""Reason-checked preparation identity cases on disposable copies only."""
import argparse,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--anchor',required=True);a=parser.parse_args()
    results=[]
    with tempfile.TemporaryDirectory(prefix='t117q-release-v2-seal-',dir='/var/tmp') as tmp:
        base=Path(tmp)
        def case(name,mutate,reason,positive=False,anchor=None):
            dest=base/name;shutil.copytree(ROOT,dest);target=mutate(dest) or dest
            run=subprocess.run([sys.executable,'-B',str(target/'verify_release_preparation.py'),'--expected-manifest-sha256',a.anchor if anchor is None else anchor],capture_output=True,text=True)
            output=run.stdout+run.stderr
            if (run.returncode==0)!=positive or reason not in output:raise ValueError((name,output))
            results.append(dict(case=name,accepted=run.returncode==0,expected_reason=reason))
        case('positive',lambda p:None,'PASS_PREPARATION_SEAL_IDENTITY_ONLY',True)
        case('wrong-anchor',lambda p:None,'external anchor mismatch',anchor='0'*64)
        case('bad-anchor',lambda p:None,'bad anchor',anchor='bad')
        def change(p):(p/'README.md').write_text('changed')
        case('changed-payload',change,'file inventory')
        case('missing-payload',lambda p:(p/'README.md').unlink(),'file inventory')
        def extra(p):(p/'extra').write_text('extra')
        case('extra-payload',extra,'file inventory')
        case('extra-directory',lambda p:(p/'extra-dir').mkdir(),'directory inventory')
        def sym(p):
            (p/'README.md').unlink();(p/'README.md').symlink_to(ROOT/'README.md')
        case('payload-symlink',sym,'symlink entry')
        def hard(p):os.link(p/'README.md',base/'hardlinked')
        case('payload-hardlink',hard,'nonregular or hardlink')
        def fifo(p):os.mkfifo(p/'fifo')
        case('fifo',fifo,'nonregular or hardlink')
        def rootlink(p):
            q=base/'root-alias';q.symlink_to(p,target_is_directory=True);return q
        case('root-symlink',rootlink,'symlink root ancestry')
        def ancestor(p):
            q=base/'ancestor-alias';q.symlink_to(base,target_is_directory=True);return q/p.name
        case('ancestor-symlink',ancestor,'symlink root ancestry')
        def manhard(p):os.link(p/'manifest.json',base/'hard-manifest')
        case('manifest-hardlink',manhard,'hardlinked file')
    print(json.dumps({'status':'PASS_SEAL_CONTROLS_ONLY','anchor':a.anchor,'results':results,'archive_created':False},indent=2))
if __name__=='__main__':main()
