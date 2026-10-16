#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT.
Read-only integrity/provenance verifier; never downloads or reseals.
"""
from pathlib import Path
import hashlib
import json
import runpy
import sys

ROOT=Path(__file__).resolve().parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check_record(record):
    name=record['path']
    path=ROOT/name
    assert path.resolve().is_relative_to(ROOT.resolve())
    data=path.read_bytes()
    assert len(data)==record['bytes'], name+' size'
    assert digest(data)==record['sha256'], name+' SHA-256'


def main():
    seal=json.loads((ROOT/'seal.json').read_text())
    actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file()}
    expected={r['path'] for r in seal['files']}
    assert actual==expected|{'seal.json'}, 'owned inventory mismatch'
    assert len(expected)==len(seal['files'])
    for r in seal['files']:
        check_record(r)
    inputs=json.loads((ROOT/'inputs-manifest.json').read_text())
    outputs=json.loads((ROOT/'outputs-manifest.json').read_text())
    left={r['path'] for r in inputs['files']}
    right={r['path'] for r in outputs['files']}
    assert not left & right
    assert left|right==expected-{'outputs-manifest.json'}
    for r in inputs['files']+outputs['files']:
        check_record(r)

    tree=json.loads((ROOT/'inputs/context/sources/preprints-tree.json').read_text())
    blobs={x['path']:x for x in tree['tree'] if x['type']=='blob'}
    fetched=json.loads((ROOT/'receipts/upstream-fetch.json').read_text())
    for r in fetched:
        data=(ROOT/'inputs/upstream'/r['path']).read_bytes()
        assert len(data)==r['bytes'] and digest(data)==r['sha256']
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert blob==r['git_blob_sha1']
        assert r['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+r['path']
        if r['path'].startswith('preprints/'):
            assert blobs[r['path']]['sha']==blob
    assert (ROOT/'inputs/upstream/LICENSE').read_bytes()==(ROOT/'inputs/context/sources/LICENSE').read_bytes()

    literature=json.loads((ROOT/'receipts/literature-fetch.json').read_text())
    for r in literature:
        if 'error' not in r:
            data=(ROOT/'inputs/literature'/r['file']).read_bytes()
            assert len(data)==r['bytes'] and digest(data)==r['sha256']
    render=runpy.run_path(str(ROOT/'checks/html_to_text.py'))['render']
    for p in (ROOT/'inputs/literature').glob('*.html'):
        assert render(p.read_text())==p.with_suffix('.txt').read_text(), str(p)

    reading=json.loads((ROOT/'receipts/read-extents.json').read_text())
    for record in reading['readings']:
        raw=(ROOT/record['path']).read_bytes()
        assert digest(raw)==record['sha256']
        lines=raw.decode().splitlines()
        for extent in record['extents']:
            start,end=extent['start_line'],extent['end_line']
            assert 1<=start<=end<=len(lines)
            passage=('\n'.join(lines[start-1:end])+'\n').encode()
            assert digest(passage)==extent['passage_sha256']

    checks=runpy.run_path(str(ROOT/'checks/check.py'))['calculate']()
    assert checks==json.loads((ROOT/'receipts/checks.json').read_text())
    print(f'PASS: {len(inputs["files"])} inputs, {len(outputs["files"])} output/dependency artifacts, '
          f'{len(fetched)} pinned upstream files, {len(reading["readings"])} reading records; exact checks reproduced')


if __name__=='__main__':
    sys.dont_write_bytecode=True
    main()
