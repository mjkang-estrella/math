#!/usr/bin/env python3
"""Copied integrity controls only. All temporary writes stay in the owned directory."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
finalhash = hashlib.sha256((root / 'FINAL.json').read_bytes()).hexdigest()

def image():
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted((root/'packet').rglob('*')) if p.is_file()} | {
            n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in ('FINAL.json','MANIFEST.json','REPORT.md')}

before = image()
cases = []

def run(name, r, ok, anchor=finalhash, missing=False):
    cmd=[sys.executable,'-B',str(r/'packet/public/verify.py'),'--root',str(r)]
    if not missing:cmd += ['--finalhash',anchor]
    q=subprocess.run(cmd,capture_output=True,text=True,timeout=25)
    good=(q.returncode==0)==ok
    cases.append({'name':name,'expected_accept':ok,'returncode':q.returncode,'control_passed':good,'stdout':q.stdout.strip(),'stderr':q.stderr.strip()})
    if not good:raise RuntimeError(name+' unexpected result')

run('real_packet_baseline',root,True)
with tempfile.TemporaryDirectory(prefix='copied-r77-',dir=root/'integrity') as tmp:
    dst=Path(tmp)
    shutil.copytree(root/'packet',dst/'packet')
    for n in ('FINAL.json','MANIFEST.json','REPORT.md'):shutil.copyfile(root/n,dst/n)
    run('copied_final_anchor_positive',dst,True)
    run('wrong_detached_finalhash',dst,False,anchor='0'*64)
    run('missing_required_finalhash',dst,False,missing=True)
    def change(name,path,data):
        old=path.read_bytes();path.write_bytes(data)
        try:run(name,dst,False)
        finally:path.write_bytes(old)
    q=dst/'packet/public/research.md'
    change('changed_research',q,q.read_bytes()+b'\nchanged\n')
    old=q.read_bytes();q.unlink();run('missing_file',dst,False);q.write_bytes(old)
    q=dst/'packet/public/extra.txt';q.write_text('extra');run('extra_file',dst,False);q.unlink()
    q=dst/'packet/public/extra-dir';q.mkdir();run('extra_empty_directory',dst,False);q.rmdir()
    q=dst/'packet/public/linked.txt';q.symlink_to('research.md');run('symlink_file',dst,False);q.unlink()
    q=dst/'packet/private/link-dir';q.symlink_to('../public',target_is_directory=True);run('symlink_directory',dst,False);q.unlink()
    q=dst/'MANIFEST.json';change('changed_manifest_old_final_anchor',q,q.read_bytes()+b' ')
    q=dst/'REPORT.md';change('changed_detached_report',q,q.read_bytes()+b'changed')
    q=dst/'FINAL.json';change('changed_final_old_detached_hash',q,q.read_bytes()+b' ')
    q=next((dst/'packet/private/upstream').rglob('projectivity.tex'))
    change('changed_canonical_source',q,q.read_bytes()+b'% changed\n')
    q=dst/'packet/private/primary/andre-1996.pdf';change('changed_primary_body',q,q.read_bytes()+b'changed')
    run('copy_restored_positive',dst,True)
run('real_packet_after_controls',root,True)
after=image()
assert before==after
receipt={'kind':'integrity-only copied controls','detached_finalhash':finalhash,'cases':cases,
         'real_packet_unchanged':before==after,'real_inventory_sha256':hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest(),
         'mathematical_gate':False}
(root/'integrity/controls.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'cases':len(cases),'all_passed':all(x['control_passed'] for x in cases),'real_packet_unchanged':before==after,'controls_sha256':hashlib.sha256((root/'integrity/controls.json').read_bytes()).hexdigest(),'finalhash':finalhash}))
