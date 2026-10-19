#!/usr/bin/env python3
"""Copied integrity controls at the supplied FINAL anchor; never edits the packet."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def snapshot(root):
    result = {}
    for p in root.rglob('*'):
        result[p.relative_to(root).as_posix()] = ('directory' if p.is_dir() else 'file', None if p.is_dir() else digest(p))
    return result

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('packet', type=Path)
    ap.add_argument('--expected-manifest-sha256', required=True)
    ap.add_argument('--work-directory', required=True, type=Path)
    args = ap.parse_args()
    original = args.packet.resolve(strict=True); work = args.work_directory.resolve(strict=True)
    if original == work or original in work.parents:
        raise ValueError('controls must be outside the original packet')
    before = snapshot(original); results = []
    with tempfile.TemporaryDirectory(prefix='r114-controls-', dir=work) as td:
        temp = Path(td); copied = temp/'packet'; shutil.copytree(original, copied)
        verifier = copied/'public/verify.py'; payload = copied/'public/report.md'
        def run(name, success=False, anchor=args.expected_manifest_sha256, root=copied):
            cmd = [sys.executable, '-B', str(verifier), str(root)]
            if anchor is not None:
                cmd += ['--expected-manifest-sha256', anchor]
            r = subprocess.run(cmd, capture_output=True, text=True)
            ok = (r.returncode == 0) == success
            results.append(dict(case=name, expected_success=success, returncode=r.returncode, satisfied=ok, stdout=r.stdout.strip(), stderr=r.stderr.strip()))
            if not ok:
                raise ValueError('unexpected control outcome: '+name)
        run('clean_copy', True)
        run('missing_external_anchor', anchor=None)
        run('wrong_external_anchor', anchor='0'*64)
        run('malformed_external_anchor', anchor='bad')
        data = payload.read_bytes(); payload.write_bytes(data+b'changed');run('changed_payload');payload.write_bytes(data)
        payload.unlink();run('missing_payload');payload.write_bytes(data)
        extra = copied/'extra';extra.write_text('x');run('extra_file');extra.unlink()
        extra.mkdir();run('extra_empty_directory');extra.rmdir()
        payload.unlink();payload.symlink_to(copied/'public/screen-184.md');run('symlink_payload');payload.unlink();payload.write_bytes(data)
        os.link(payload,extra);run('hardlink');extra.unlink()
        os.mkfifo(extra);run('fifo');extra.unlink()
        extra = copied/'public/manifest.json';extra.write_text('{}');run('nested_manifest');extra.unlink()
        m = copied/'manifest.json';mb=m.read_bytes();m.write_bytes(mb+b'\n');run('changed_manifest');m.write_bytes(mb)
        payload.write_bytes(data+b'changed');mf=json.loads(mb)
        for e in mf['entries']:
            if e['path']=='public/report.md':e.update(size=payload.stat().st_size,sha256=digest(payload))
        m.write_text(json.dumps(mf,indent=2)+'\n');run('self_reseal_at_original_final_anchor');m.write_bytes(mb);payload.write_bytes(data)
        rootlink=temp/'rootlink';rootlink.symlink_to(copied,target_is_directory=True);run('symlink_root',root=rootlink)
        ancestor=temp/'ancestor';ancestor.symlink_to(temp,target_is_directory=True);run('symlink_ancestor',root=ancestor/'packet')
        run('restored_copy',True)
    after=snapshot(original)
    if before!=after:raise ValueError('original packet changed')
    print(json.dumps(dict(status='copied_integrity_controls_only',manifest_sha256=args.expected_manifest_sha256,original_packet_unchanged=True,cases=results),indent=2,sort_keys=True))

if __name__=='__main__':main()
