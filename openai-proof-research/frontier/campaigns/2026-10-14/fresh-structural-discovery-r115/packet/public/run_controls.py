#!/usr/bin/env python3
"""Run final-anchor controls on disposable copies; original packet is read-only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

def sha(b):
    return hashlib.sha256(b).hexdigest()

def snapshot(root):
    rows=[]
    for p in sorted(root.rglob('*')):
        rel=p.relative_to(root).as_posix()
        if p.is_symlink(): rows.append((rel,'symlink',os.readlink(p)))
        elif p.is_dir(): rows.append((rel,'directory'))
        else: rows.append((rel,'file',sha(p.read_bytes())))
    return sha(json.dumps(rows,separators=(',',':')).encode())

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet',type=Path,required=True)
    ap.add_argument('--expected-manifest-sha256',required=True)
    ap.add_argument('--controls-dir',type=Path,required=True)
    a=ap.parse_args(); original=a.packet.resolve(); out=a.controls_dir.resolve()
    if out==original or original in out.parents:
        raise ValueError('controls directory must be outside packet')
    out.mkdir(parents=True,exist_ok=True)
    verifier=original/'public/verify.py'; before=snapshot(original); rows=[]
    cases=[('baseline',None),('wrong-anchor','anchor mismatch'),('missing-anchor','required'),
           ('payload-mutation','payload content'),('missing-payload','inventory mismatch'),
           ('extra-file','inventory mismatch'),('extra-directory','inventory mismatch'),
           ('file-symlink','symlink forbidden'),('directory-symlink','symlink forbidden'),
           ('manifest-mutation','anchor mismatch'),('rehashed-forgery','anchor mismatch'),
           ('file-replaced-with-directory','payload content')]
    try:
        for name,reason in cases:
            copy=out/('copy-'+name)
            if copy.exists(): raise ValueError('refusing existing control copy: '+str(copy))
            shutil.copytree(original,copy)
            f=copy/'public/report.md'
            if name=='payload-mutation': f.write_bytes(f.read_bytes()+b'\nmutation\n')
            elif name=='missing-payload': f.unlink()
            elif name=='extra-file': (copy/'unexpected').write_text('extra')
            elif name=='extra-directory': (copy/'unexpected-empty').mkdir()
            elif name=='file-symlink': f.unlink();f.symlink_to(copy/'public/README.md')
            elif name=='directory-symlink': (copy/'linked-directory').symlink_to(copy/'private',target_is_directory=True)
            elif name=='manifest-mutation':
                q=copy/'manifest.json';q.write_bytes(q.read_bytes()+b'\n')
            elif name=='rehashed-forgery':
                f.write_bytes(f.read_bytes()+b'\nforged\n')
                q=copy/'manifest.json';d=json.loads(q.read_text())
                for e in d['entries']:
                    if e['path']=='public/report.md':e['bytes']=f.stat().st_size;e['sha256']=sha(f.read_bytes())
                q.write_text(json.dumps(d,indent=2)+'\n')
                (copy/'FORGED-ANCHOR.sha256').write_text(sha(q.read_bytes())+'\n')
            elif name=='file-replaced-with-directory':f.unlink();f.mkdir()
            cmd=[sys.executable,'-B',str(verifier),'--packet',str(copy)]
            if name!='missing-anchor':cmd += ['--expected-manifest-sha256','0'*64 if name=='wrong-anchor' else a.expected_manifest_sha256]
            r=subprocess.run(cmd,capture_output=True,text=True)
            good=(r.returncode==0) if name=='baseline' else (r.returncode!=0 and reason in r.stderr)
            rows.append({'case':name,'expected':'accept' if name=='baseline' else 'reject','returncode':r.returncode,'expected_reason_seen':good,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
            shutil.rmtree(copy)
            if not good:raise AssertionError('control failed: '+name)
    finally:
        after=snapshot(original)
        result={'manifest_sha256_external_final':a.expected_manifest_sha256,'original_before_sha256':before,'original_after_sha256':after,'original_unchanged':before==after,'all_expected':len(rows)==len(cases) and all(r['expected_reason_seen'] for r in rows),'mathematical_gate':False,'cases':rows}
        (out/'final-anchor-controls.json').write_text(json.dumps(result,indent=2)+'\n')
    if not result['original_unchanged'] or not result['all_expected']:return 1
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},sort_keys=True))
    return 0

if __name__=='__main__':sys.exit(main())
