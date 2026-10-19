#!/usr/bin/env python3
"""Copied integrity controls only. Temporary writes stay in the owned packet.
Run without concurrent readers; temporary directories are removed on exit.
The authenticated original verifier checks copies; never execute mutated code.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--finalhash',required=True)
    args=ap.parse_args()
    root=Path(__file__).absolute().parent
    verifier=root/'verify.py'
    def run(where,anchor=args.finalhash):
        return subprocess.run([sys.executable,'-B',str(verifier),'--root',str(where),'--finalhash',anchor],capture_output=True,text=True)
    baseline=run(root)
    if baseline.returncode:
        raise RuntimeError('Original baseline failed: '+baseline.stderr)
    m=json.loads((root/'MANIFEST.json').read_text())
    outcomes={}
    with tempfile.TemporaryDirectory(prefix='.integrity-controls-',dir=root) as tmp:
        parent=Path(tmp)
        def clone(name):
            dest=parent/name;dest.mkdir()
            for d in m['directories']:(dest/d).mkdir(parents=True,exist_ok=True)
            for f in ['MANIFEST.json']+[r['path'] for r in m['files']]:
                shutil.copyfile(root/f,dest/f)
            return dest
        def case(name,mutation=None,accept=False,anchor=args.finalhash):
            dest=clone(name)
            if mutation:mutation(dest)
            result=run(dest,anchor)
            passed=(result.returncode==0)==accept
            outcomes[name]={'expected':'accept' if accept else 'reject','observed':'accept' if result.returncode==0 else 'reject','control_passed':passed}
            if not passed:raise RuntimeError(name+': '+result.stdout+result.stderr)
        def alter(dest,name):
            q=dest/name;q.write_bytes(q.read_bytes()+b'\nMUTATION\n')
        def symlink(dest):
            (dest/'README.md').unlink();(dest/'README.md').symlink_to('research.md')
        def hardlink(dest):
            (dest/'README.md').unlink();os.link(dest/'research.md',dest/'README.md')
        def self_reseal(dest):
            alter(dest,'research.md')
            manifest=json.loads((dest/'MANIFEST.json').read_text())
            for row in manifest['files']:
                if row['path']=='research.md':
                    raw=(dest/row['path']).read_bytes();row.update(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
            (dest/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
        case('clean_copy',accept=True)
        case('wrong_detached_anchor',anchor=('1' if args.finalhash[0]!='1' else '2')+args.finalhash[1:])
        case('altered_research',lambda d:alter(d,'research.md'))
        case('altered_scope',lambda d:alter(d,'scope-freeze.md'))
        case('altered_verifier_payload',lambda d:alter(d,'verify.py'))
        case('missing_payload',lambda d:(d/'README.md').unlink())
        case('extra_file',lambda d:(d/'unexpected.txt').write_text('extra'))
        case('extra_empty_directory',lambda d:(d/'unexpected-directory').mkdir())
        case('symbolic_payload',symlink)
        case('hardlinked_payload',hardlink)
        case('self_resealed_manifest',self_reseal)
        case('private_body_tamper',lambda d:alter(d,m['files'][-1]['path']) if m['files'][-1]['path'].startswith('private/') else alter(d,'private/primary/Gupta-1309.1368v1.txt'))
        missing=subprocess.run([sys.executable,'-B',str(verifier),'--root',str(clone('missing-anchor'))],capture_output=True,text=True)
        outcomes['missing_detached_anchor']={'expected':'reject','observed':'reject' if missing.returncode else 'accept','control_passed':bool(missing.returncode)}
        if not missing.returncode:raise RuntimeError('Missing anchor accepted')
    final=run(root)
    if final.returncode:raise RuntimeError('Post-cleanup baseline failed: '+final.stderr)
    print(json.dumps({'controls':outcomes,'post_cleanup_integrity':'verified','mathematical_gate':False},indent=2,sort_keys=True))

if __name__=='__main__':main()
