#!/usr/bin/env python3
"""Disposable copy controls; no mathematical verdict. SPDX-License-Identifier: MIT."""
import argparse,hashlib,json,os,shutil,subprocess,tempfile
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);p.add_argument('--scratch',default='/var/tmp');a=p.parse_args()
root=Path(os.path.abspath(__file__)).parent
results=[]
def run(path,anchor,reason):
    r=subprocess.run(['python3','-B',str(path/'verify.py'),'--anchor',anchor],capture_output=True,text=True)
    ok=(r.returncode==0) if reason is None else (r.returncode!=0 and reason in r.stderr)
    if not ok:raise RuntimeError(str((path,reason,r.returncode,r.stdout,r.stderr)))
    results.append({'case':name,'expected_reason':reason,'exit_code':r.returncode,'pass':ok})
# No verification imports, no mutation of original tree.
with tempfile.TemporaryDirectory(prefix='t027o-manuscript-controls-',dir=a.scratch) as tmp:
    t=Path(tmp)
    cases=['positive','wrong-anchor','payload-byte','missing-file','extra-file','extra-directory','root-link','ancestor-link','payload-link','hardlink','fifo','nested-manifest','manifest-hardlink','self-reseal']
    for name in cases:
        d=t/name;shutil.copytree(root,d);invoke=d;anchor=a.anchor;reason=None
        payload=d/'public/sections/01-context.tex'
        if name=='wrong-anchor':anchor='0'*64;reason='external manifest anchor mismatch'
        elif name=='payload-byte':payload.write_bytes(payload.read_bytes()+b'\n');reason='exact inventory mismatch'
        elif name=='missing-file':payload.unlink();reason='exact inventory mismatch'
        elif name=='extra-file':(d/'extra').write_text('x');reason='exact inventory mismatch'
        elif name=='extra-directory':(d/'empty').mkdir();reason='exact inventory mismatch'
        elif name=='root-link':invoke=t/'linked-root';invoke.symlink_to(d,target_is_directory=True);reason='symlink ancestry'
        elif name=='ancestor-link':
            parent=t/'ancestor';parent.mkdir();shutil.move(str(d),parent/'packet');link=t/'linked-ancestor';link.symlink_to(parent,target_is_directory=True);invoke=link/'packet';reason='symlink ancestry'
        elif name=='payload-link':payload.unlink();payload.symlink_to(d/'public/article.tex');reason='symlink payload'
        elif name=='hardlink':os.link(payload,d/'hard-copy');reason='hardlink'
        elif name=='fifo':os.mkfifo(d/'pipe');reason='nonregular entry'
        elif name=='nested-manifest':(d/'public/manifest.json').write_text('{}');reason='nested manifest'
        elif name=='manifest-hardlink':os.link(d/'manifest.json',d/'manifest-copy');reason='manifest nonregular or hardlink'
        elif name=='self-reseal':
            payload.write_bytes(payload.read_bytes()+b'\n');m=json.loads((d/'manifest.json').read_text());m['files']['public/sections/01-context.tex']={'bytes':payload.stat().st_size,'sha256':hashlib.sha256(payload.read_bytes()).hexdigest()};(d/'manifest.json').write_text(json.dumps(m,sort_keys=True,indent=2)+'\n');reason='external manifest anchor mismatch'
        run(invoke,anchor,reason)
        for child in list(t.iterdir()):
            if child.is_symlink() or child.is_file(): child.unlink()
            else: shutil.rmtree(child)
print(json.dumps({'result':'PASS_COPIED_IDENTITY_CONTROLS','cases':results},indent=2))
