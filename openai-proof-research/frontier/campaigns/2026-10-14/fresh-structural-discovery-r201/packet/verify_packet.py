#!/usr/bin/env python3
"""Read-only exact-selection artifact verifier. No mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

sys.dont_write_bytecode = True

def digest(path):
    with path.open('rb') as f:
        h=hashlib.sha256()
        for block in iter(lambda:f.read(1024*1024),b''):
            h.update(block)
    return h.hexdigest()

def mode(path):
    return f'{stat.S_IMODE(path.lstat().st_mode):04o}'

def inventory(root):
    files={}
    dirs={'.':mode(root)}
    def visit(p):
        with os.scandir(p) as it:
            for e in it:
                q=p/e.name
                rel=q.relative_to(root).as_posix()
                if e.is_symlink():
                    raise ValueError('symlink not admitted: '+rel)
                if e.is_dir(follow_symlinks=False):
                    dirs[rel]=mode(q)
                    visit(q)
                elif e.is_file(follow_symlinks=False):
                    if rel!='MANIFEST.json':
                        files[rel]=q
                else:
                    raise ValueError('nonregular entry: '+rel)
    visit(root)
    return files,dirs

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--packet',required=True)
    ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--report',required=True)
    ap.add_argument('--report-sha256',required=True)
    a=ap.parse_args()
    root=Path(a.packet)
    report=Path(a.report)
    if root.is_symlink() or report.is_symlink():
        raise ValueError('anchor path is a symlink')
    manifest=root/'MANIFEST.json'
    final=root/'FINAL.md'
    for p,expected,label in [
        (manifest,a.manifest_sha256,'MANIFEST'),
        (final,a.final_sha256,'FINAL'),
        (report,a.report_sha256,'outside REPORT')]:
        if len(expected)!=64 or any(ch not in '0123456789abcdef' for ch in expected):
            raise ValueError('invalid explicit '+label+' anchor')
        if digest(p)!=expected:
            raise ValueError(label+' detached anchor mismatch')
    data=json.loads(manifest.read_bytes())
    if data.get('schema')!='r201-exact-selection-v1':
        raise ValueError('unsupported manifest schema')
    if mode(manifest)!=data['manifest_mode'] or mode(report)!=data['outside_report_mode']:
        raise ValueError('manifest/report mode mismatch')
    expected={}
    for rec in data['files']:
        rel=rec['path']
        parsed=PurePosixPath(rel)
        if parsed.is_absolute() or '..' in parsed.parts or str(parsed)!=rel or rel=='MANIFEST.json':
            raise ValueError('noncanonical selected path')
        if rel in expected:
            raise ValueError('duplicate selected path')
        expected[rel]=rec
    if 'FINAL.md' not in expected or expected['FINAL.md']['sha256']!=a.final_sha256:
        raise ValueError('FINAL not bound to exact selection')
    actual,dirs=inventory(root)
    if set(actual)!=set(expected):
        raise ValueError('exact file selection differs')
    if dirs!=data['directories']:
        raise ValueError('exact directory selection/modes differ')
    for rel,p in actual.items():
        rec=expected[rel]
        if p.stat().st_size!=rec['bytes'] or mode(p)!=rec['mode'] or digest(p)!=rec['sha256']:
            raise ValueError('selected bytes/mode mismatch: '+rel)
    print(json.dumps({'artifact_verification':'PASS','mathematical_gate':False,
        'selected_files':len(actual),'selected_bytes':sum(e['bytes'] for e in expected.values()),
        'final_sha256':a.final_sha256,'manifest_sha256':a.manifest_sha256,
        'outside_report_sha256':a.report_sha256},indent=2))

if __name__=='__main__':
    try:
        main()
    except Exception as exc:
        print('ARTIFACT REJECT: '+str(exc),file=sys.stderr)
        sys.exit(1)
