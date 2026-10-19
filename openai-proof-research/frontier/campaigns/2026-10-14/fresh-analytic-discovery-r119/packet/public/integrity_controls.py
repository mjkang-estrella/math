#!/usr/bin/env python3
"""Disposable-copy integrity controls; not mathematical tests."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def protected(root):
    names = [p for p in (root/'packet').rglob('*') if p.is_file()]
    names += [root/n for n in ['FINAL.json','MANIFEST.json','REPORT.md']]
    return {p.relative_to(root).as_posix():sha(p) for p in sorted(names)}

def reseal(copy):
    m = json.loads((copy/'MANIFEST.json').read_text())
    m['files'] = {p.relative_to(copy/'packet').as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)}
                  for p in sorted((copy/'packet').rglob('*')) if p.is_file()}
    m['directories'] = sorted(p.relative_to(copy/'packet').as_posix()
                              for p in (copy/'packet').rglob('*') if p.is_dir())
    (copy/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
    f = json.loads((copy/'FINAL.json').read_text())
    f['manifest_sha256'] = sha(copy/'MANIFEST.json')
    f['packet_report_sha256'] = sha(copy/'packet/public/report.md')
    (copy/'FINAL.json').write_text(json.dumps(f,indent=2,sort_keys=True)+'\n')
    return sha(copy/'FINAL.json')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',required=True,type=Path)
    ap.add_argument('--tree',required=True,type=Path)
    ap.add_argument('--finalhash',required=True)
    ap.add_argument('--reporthash',required=True)
    args=ap.parse_args(); root=args.root.resolve(); tree=args.tree.resolve()
    assert sha(root/'FINAL.json')==args.finalhash and sha(root/'REPORT.md')==args.reporthash
    before=protected(root); controls=root/'controls';controls.mkdir(exist_ok=True)
    cases=[('baseline','INTEGRITY_ONLY_OK'),('missing-final','--finalhash'),('missing-report','--reporthash'),
           ('wrong-final','detached-finalhash-mismatch'),('wrong-report','detached-reporthash-mismatch'),
           ('changed-final','detached-finalhash-mismatch'),('changed-manifest','manifest-hash-mismatch'),
           ('changed-report','detached-reporthash-mismatch'),('changed-payload','packet-payload-mismatch'),
           ('missing-payload','packet-file-inventory-mismatch'),('extra-file','packet-file-inventory-mismatch'),
           ('extra-directory','packet-directory-inventory-mismatch'),('file-symlink','nonregular-or-linked-file'),
           ('directory-symlink','nonregular-directory'),('hardlink','nonregular-or-linked-file'),
           ('wrong-tree','canonical-tree-hash-mismatch'),('coherent-reseal-old-anchor','detached-finalhash-mismatch'),
           ('source-url-new-test-anchor','canonical-url'),('primary-hash-new-test-anchor','primary-representation')]
    results=[]
    for name,expected in cases:
        with tempfile.TemporaryDirectory(prefix='case-',dir=controls) as td:
            tmp=Path(td);cp=tmp/'copy';cp.mkdir();shutil.copytree(root/'packet',cp/'packet')
            for n in ['FINAL.json','MANIFEST.json','REPORT.md']:shutil.copy2(root/n,cp/n)
            fh=args.finalhash;rh=args.reporthash;tp=tree;payload=cp/'packet/public/README.md'
            if name=='wrong-final':fh='0'*64
            elif name=='wrong-report':rh='0'*64
            elif name=='changed-final':(cp/'FINAL.json').write_bytes((cp/'FINAL.json').read_bytes()+b' ')
            elif name=='changed-manifest':(cp/'MANIFEST.json').write_bytes((cp/'MANIFEST.json').read_bytes()+b' ')
            elif name=='changed-report':(cp/'REPORT.md').write_bytes((cp/'REPORT.md').read_bytes()+b' ')
            elif name in ('changed-payload','coherent-reseal-old-anchor'):
                payload.write_bytes(payload.read_bytes()+b' ')
                if name=='coherent-reseal-old-anchor':reseal(cp)
            elif name=='missing-payload':payload.unlink()
            elif name=='extra-file':(cp/'packet/extra.txt').write_text('extra')
            elif name=='extra-directory':(cp/'packet/extra').mkdir()
            elif name=='file-symlink':payload.unlink();payload.symlink_to(cp/'REPORT.md')
            elif name=='directory-symlink':(cp/'packet/extra').symlink_to(cp/'packet/public',target_is_directory=True)
            elif name=='hardlink':os.link(payload,cp/'packet/linked.txt')
            elif name=='wrong-tree':tp=tmp/'wrong-tree.json';tp.write_bytes(tree.read_bytes()+b' ')
            elif name=='source-url-new-test-anchor':
                q=cp/'packet/public/source-register.json';data=json.loads(q.read_text());data[0]['url']+='?changed';q.write_text(json.dumps(data));fh=reseal(cp)
            elif name=='primary-hash-new-test-anchor':
                q=cp/'packet/public/primary-register.json';data=json.loads(q.read_text());next(e for e in data if e['status']=='success')['pdf_sha256']='0'*64;q.write_text(json.dumps(data));fh=reseal(cp)
            cmd=[sys.executable,'-B',str(cp/'packet/public/verify.py'),'--root',str(cp),'--tree',str(tp)]
            if name!='missing-final':cmd+=['--finalhash',fh]
            if name!='missing-report':cmd+=['--reporthash',rh]
            done=subprocess.run(cmd,capture_output=True,text=True)
            output=done.stdout+done.stderr
            ok=((done.returncode==0)==(name=='baseline') and expected in output)
            results.append({'case':name,'expected':expected,'exit_code':done.returncode,'reason_matched':ok,'output':output.strip()})
            if not ok:print(json.dumps(results[-1]),file=sys.stderr)
    after=protected(root)
    receipt={'purpose':'INTEGRITY_ONLY_NOT_MATHEMATICAL_GATES','final_sha256':args.finalhash,'report_sha256':args.reporthash,
             'control_program_sha256':sha(root/'packet/public/integrity_controls.py'),'original_protected_before':before,
             'original_protected_after':after,'original_unchanged':before==after,'cases':results,
             'all_expected':all(x['reason_matched'] for x in results),'temporary_copies_removed':True}
    (controls/'integrity-controls.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'cases':len(results),'all_expected':receipt['all_expected'],'original_unchanged':before==after,
                      'receipt_sha256':sha(controls/'integrity-controls.json')}))
    return 0 if receipt['all_expected'] and before==after else 1

if __name__=='__main__':sys.exit(main())
