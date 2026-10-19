#!/usr/bin/env python3
"""Mutate disposable copies only. Prints an integrity receipt, never a math gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

H=lambda b:hashlib.sha256(b).hexdigest()
def snapshot(p):
    return [(str(f.relative_to(p)),H(f.read_bytes()) if f.is_file() else 'directory') for f in sorted(p.rglob('*'))]
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet',required=True,type=Path)
    ap.add_argument('--expected-finalhash',required=True)
    ap.add_argument('--scratch-parent',required=True,type=Path)
    a=ap.parse_args(); src=a.packet.resolve(); scratch=a.scratch_parent.resolve()
    if scratch!=src.parent: raise ValueError('scratch-parent must be the campaign-owned parent of packet')
    before=snapshot(src); results=[]; verifier=src/'public/code/verify_packet.py'
    def call(p,expected):
        cmd=[sys.executable,'-B',str(verifier),'--packet',str(p)]
        if expected is not None: cmd+=['--expected-finalhash',expected]
        r=subprocess.run(cmd,text=True,capture_output=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        return r
    def record(name,r,want):
        ok=(r.returncode==0)==want
        results.append({'name':name,'expected_accept':want,'exit_code':r.returncode,'matched_expectation':ok,'output':(r.stdout+r.stderr).strip()})
        if not ok: raise AssertionError(name+': '+r.stdout+r.stderr)
    record('original_read_only',call(src,a.expected_finalhash),True)
    def manifest_edit(p,fn):
        f=p/'manifest.json'; m=json.loads(f.read_bytes());fn(m);f.write_text(json.dumps(m,sort_keys=True,indent=2)+'\n');return H(f.read_bytes())
    def refresh(p,s):
        f=p/s
        return manifest_edit(p,lambda m:[r.update({'bytes':f.stat().st_size,'sha256':H(f.read_bytes())}) for r in m['files'] if r['path']==s])
    def mutate(p,name):
        expected=a.expected_finalhash
        if name=='clean_copy': pass
        elif name=='missing_detached_argument': expected=None
        elif name=='wrong_detached_hash': expected='0'*64
        elif name=='changed_payload': (p/'public/research-report.md').write_text('changed')
        elif name=='missing_payload': (p/'public/research-report.md').unlink()
        elif name=='extra_file': (p/'extra.txt').write_text('extra')
        elif name=='extra_directory': (p/'extra-directory').mkdir()
        elif name=='symlink': (p/'extra-link').symlink_to('public/research-report.md')
        elif name=='fifo': os.mkfifo(p/'extra-fifo')
        elif name=='manifest_changed_same_anchor': (p/'manifest.json').write_bytes((p/'manifest.json').read_bytes()+b' ')
        elif name=='duplicate_entry_new_anchor': expected=manifest_edit(p,lambda m:m['files'].append(dict(m['files'][0])))
        elif name=='traversal_entry_new_anchor': expected=manifest_edit(p,lambda m:m['files'][0].update(path='../outside'))
        elif name=='absolute_entry_new_anchor': expected=manifest_edit(p,lambda m:m['files'][0].update(path='/outside'))
        elif name=='bool_size_new_anchor': expected=manifest_edit(p,lambda m:m['files'][0].update(bytes=True))
        elif name=='duplicate_key_new_anchor':
            f=p/'manifest.json'; f.write_bytes(b'{"schema":"t085e111-exact-packet-v1",'+f.read_bytes()[1:]); expected=H(f.read_bytes())
        elif name=='raw_blob_receipt_new_anchor':
            s='private/source-provenance.json'; f=p/s;m=json.loads(f.read_bytes());m[0]['git_blob']='0'*40;f.write_text(json.dumps(m));expected=refresh(p,s)
        elif name=='primary_receipt_new_anchor':
            s='private/primary/provenance.json';f=p/s;m=json.loads(f.read_bytes());m[0]['sha256']='0'*64;f.write_text(json.dumps(m));expected=refresh(p,s)
        elif name=='frozen_target_new_anchor':
            s='public/frozen-target.md';(p/s).write_bytes((p/s).read_bytes()+b'changed');expected=refresh(p,s)
        elif name=='prefreeze_screen_new_anchor':
            s='public/pre-freeze-screen.md';(p/s).write_bytes((p/s).read_bytes()+b'changed');expected=refresh(p,s)
        elif name=='disposition_identity_new_anchor': expected=manifest_edit(p,lambda m:m.update(status='CLAIMED_COMPLETE'))
        else: raise ValueError(name)
        return expected
    cases=['clean_copy','missing_detached_argument','wrong_detached_hash','changed_payload','missing_payload','extra_file','extra_directory','symlink','fifo','manifest_changed_same_anchor','duplicate_entry_new_anchor','traversal_entry_new_anchor','absolute_entry_new_anchor','bool_size_new_anchor','duplicate_key_new_anchor','raw_blob_receipt_new_anchor','primary_receipt_new_anchor','frozen_target_new_anchor','prefreeze_screen_new_anchor','disposition_identity_new_anchor']
    for name in cases:
        with tempfile.TemporaryDirectory(prefix='integrity-copy-',dir=scratch) as temp:
            cp=Path(temp)/'packet';shutil.copytree(src,cp)
            expected=mutate(cp,name);record(name,call(cp,expected),name=='clean_copy')
    if snapshot(src)!=before: raise AssertionError('sealed packet changed during controls')
    record('original_after_controls',call(src,a.expected_finalhash),True)
    print(json.dumps({'kind':'copied integrity controls; not mathematical or contribution gates','finalhash':a.expected_finalhash,'sealed_packet_bytes_and_inventory_unchanged':True,'cases':results,'all_expected_outcomes_observed':True},sort_keys=True,indent=2))
if __name__=='__main__': main()
