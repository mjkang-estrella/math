#!/usr/bin/env python3
"""Run integrity controls on disposable owned copies; no mathematical tests."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys


def h(b):
    return hashlib.sha256(b).hexdigest()


def snapshot(root):
    result = {}
    for p in sorted((root / 'packet').rglob('*')):
        s = p.lstat()
        rel = p.relative_to(root).as_posix()
        result[rel] = {'mode': stat.S_IMODE(s.st_mode), 'type':stat.S_IFMT(s.st_mode)}
        if p.is_file():
            result[rel]['sha256'] = h(p.read_bytes())
            result[rel]['nlink'] = s.st_nlink
    for n in ['MANIFEST.json','FINAL.json']:
        result[n] = h((root / n).read_bytes())
    return result


def dump(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True)+'\n')


def main():
    a = argparse.ArgumentParser()
    a.add_argument('--root',required=True)
    a.add_argument('--tree',required=True)
    a.add_argument('--finalhash',required=True)
    a.add_argument('--reporthash',required=True)
    args = a.parse_args()
    root = Path(args.root).resolve(); tree = Path(args.tree).resolve()
    controls = root / 'controls'
    controls.mkdir(exist_ok=True)
    temp = controls / 'working-copy'
    if temp.exists():
        raise RuntimeError('refusing to overwrite existing control working-copy')
    before = snapshot(root)
    verifier = root / 'packet/public/verify.py'
    cases = []
    def run(name, mutate=None, drop=None, replacements=None, expected=None, tree_mutate=None):
        temp.mkdir()
        try:
            shutil.copytree(root/'packet',temp/'packet')
            shutil.copyfile(root/'MANIFEST.json',temp/'MANIFEST.json')
            shutil.copyfile(root/'FINAL.json',temp/'FINAL.json')
            localtree = tree
            if tree_mutate:
                localtree = temp/'tree-copy.json'
                shutil.copyfile(tree,localtree)
                tree_mutate(localtree)
            if mutate: mutate(temp)
            vals = {'--root':str(temp),'--tree':str(localtree),'--finalhash':args.finalhash,'--reporthash':args.reporthash}
            if drop: del vals[drop]
            vals.update(replacements or {})
            cmd = [sys.executable,str(verifier)]
            for key,val in vals.items():cmd.extend([key,val])
            r = subprocess.run(cmd, capture_output=True, text=True)
            ok = r.returncode == 0 if expected is None else r.returncode != 0 and expected in r.stderr
            cases.append({'name':name,'expected':'accept' if expected is None else 'reject: '+expected,'returncode':r.returncode,'passed':ok,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
            if not ok: raise RuntimeError('unexpected control outcome: '+name)
        finally:
            shutil.rmtree(temp)
    report = lambda c:c/'packet/public/report.md'
    def mutate_report(c): report(c).write_bytes(report(c).read_bytes()+b'\nchanged\n')
    def symlink_file(c):
        report(c).unlink();report(c).symlink_to(c/'packet/public/packing.md')
    def symlink_dir(c): (c/'packet/linkdir').symlink_to(c/'packet/public',target_is_directory=True)
    def hardlink(c):
        shutil.copyfile(report(c),c/'link-target');report(c).unlink();os.link(c/'link-target',report(c))
    def coherent(c):
        mutate_report(c)
        m=json.loads((c/'MANIFEST.json').read_text())
        for r in m['files']:
            if r['path']=='public/report.md':r['sha256']=h(report(c).read_bytes());r['bytes']=report(c).stat().st_size
        dump(c/'MANIFEST.json',m)
        f=json.loads((c/'FINAL.json').read_text());f['manifest_sha256']=h((c/'MANIFEST.json').read_bytes());f['report_sha256']=h(report(c).read_bytes());dump(c/'FINAL.json',f)
    def altered_tree(p):
        t=json.loads(p.read_text());t['truncated']=True;dump(p,t)
    run('positive')
    run('missing-final-anchor',drop='--finalhash',expected='--finalhash')
    run('wrong-final-anchor',replacements={'--finalhash':'0'*64},expected='external FINAL hash mismatch')
    run('missing-report-anchor',drop='--reporthash',expected='--reporthash')
    run('wrong-report-anchor',replacements={'--reporthash':'0'*64},expected='external report hash mismatch')
    run('malformed-final-anchor',replacements={'--finalhash':'not-a-hash'},expected='invalid external finalhash')
    run('report-tamper',mutate_report,expected='packet file inventory/hash/mode mismatch')
    run('missing-file',lambda c:report(c).unlink(),expected='packet file inventory/hash/mode mismatch')
    run('extra-file',lambda c:(c/'packet/extra.txt').write_text('extra'),expected='packet file inventory/hash/mode mismatch')
    run('extra-empty-directory',lambda c:(c/'packet/extra-dir').mkdir(),expected='packet directory inventory/mode mismatch')
    run('symlink-file',symlink_file,expected='not a regular file')
    run('symlink-directory',symlink_dir,expected='non-directory/symlink')
    run('hardlink-file',hardlink,expected='hard link')
    run('file-mode',lambda c:report(c).chmod(0o600),expected='packet file inventory/hash/mode mismatch')
    run('directory-mode',lambda c:(c/'packet/public').chmod(0o700),expected='packet directory inventory/mode mismatch')
    run('manifest-tamper',lambda c:(c/'MANIFEST.json').write_bytes((c/'MANIFEST.json').read_bytes()+b' '),expected='manifest hash mismatch')
    run('final-tamper',lambda c:(c/'FINAL.json').write_bytes((c/'FINAL.json').read_bytes()+b' '),expected='external FINAL hash mismatch')
    run('coherently-resealed-under-old-anchor',coherent,expected='external FINAL hash mismatch')
    run('altered-complete-tree',tree_mutate=altered_tree,expected='complete tree bytes mismatch')
    def first_upstream(c):
        p=next((c/'packet/private/upstream').rglob('*.tex'));p.write_bytes(p.read_bytes()+b' ')
    run('upstream-tamper',first_upstream,expected='packet file inventory/hash/mode mismatch')
    def first_primary(c):
        p=next((c/'packet/private/primary').glob('*.pdf'));p.write_bytes(p.read_bytes()+b' ')
    run('primary-tamper',first_primary,expected='packet file inventory/hash/mode mismatch')
    run('verifier-copy-tamper',lambda c:(c/'packet/public/verify.py').write_bytes((c/'packet/public/verify.py').read_bytes()+b'\n# changed\n'),expected='packet file inventory/hash/mode mismatch')
    run('positive-after-negative-controls')
    after = snapshot(root)
    if before != after:raise RuntimeError('original changed')
    result={'format':1,'final_sha256':args.finalhash,'report_sha256':args.reporthash,'case_count':len(cases),'all_passed':all(r['passed'] for r in cases),'original_unchanged':True,'original_snapshot_sha256':h(json.dumps(before,sort_keys=True).encode()),'mathematical_gate':False,'runner':'Trusted original verifier invoked read-only against disposable packet copies; originals were compared before/after.','cases':cases}
    dump(controls/'results.json',result)
    print(json.dumps({k:result[k] for k in ['case_count','all_passed','original_unchanged','mathematical_gate']},sort_keys=True))


if __name__=='__main__':main()
