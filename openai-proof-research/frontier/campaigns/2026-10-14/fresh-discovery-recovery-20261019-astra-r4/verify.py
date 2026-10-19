#!/usr/bin/env python3
"""Read-only packet verifier; no network, mutation, or theorem certification."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parent

def sha(data): return hashlib.sha256(data).hexdigest()

def checked_path(rel):
    p=ROOT/rel
    assert not p.is_symlink(), f'symlink forbidden: {rel}'
    assert p.resolve().is_relative_to(ROOT), f'outside packet: {rel}'
    return p

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--private',action='store_true',help='Verify locally retained private provenance as well.')
    args=ap.parse_args()
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    assert manifest['status']=='FULL TARGET PROVED; TECHNICAL; NO SUBSTANTIAL NOMINEE'
    records=manifest['public_files']+(manifest['private_files'] if args.private else [])
    for item in records:
        data=checked_path(item['path']).read_bytes()
        assert len(data)==item['bytes'] and sha(data)==item['sha256'], item['path']
    public_actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and 'private' not in p.relative_to(ROOT).parts and p.name!='MANIFEST.json'}
    assert public_actual=={r['path'] for r in manifest['public_files']}, 'public inventory mismatch'
    for path,want in manifest['immutable_freezes'].items():
        assert sha(checked_path(path).read_bytes())==want,path
    result=subprocess.run([sys.executable,'-B',str(ROOT/'diagnostics.py')],check=True,capture_output=True,text=True)
    assert json.loads(result.stdout)==json.loads((ROOT/'diagnostics.json').read_text()),'diagnostics mismatch'
    if args.private:
        for item in json.loads((ROOT/'source-receipts.json').read_text()):
            data=checked_path(item['path']).read_bytes()
            assert sha(data)==item['sha256']
            assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==item['git_blob']
        for item in json.loads((ROOT/'primary-receipts.json').read_text()):
            pdf=item.get('path',item.get('pdf_path'))
            assert sha(checked_path(pdf).read_bytes())==item.get('sha256',item.get('pdf_sha256'))
            txt=item.get('text_path',str(Path(pdf).with_suffix('.txt')))
            assert sha(checked_path(txt).read_bytes())==item['text_sha256']
        hist=json.loads((ROOT/'history-receipts.json').read_text())
        for item in hist['copies']:
            assert sha(checked_path(item['copy']).read_bytes())==item['sha256']
        tree=json.loads((ROOT/'private/context/sources/preprints-tree.json').read_text())
        assert tree.get('truncated') is False
        assert len(tree['tree'])==13223
    print(json.dumps({'status':'PASS','public_files':len(manifest['public_files']),'private_verified':args.private,'manifest_sha256':sha((ROOT/'MANIFEST.json').read_bytes()),'limits':'Integrity and finite exact diagnostics only; no independent mathematical review or campaign acceptance.'},indent=2))

if __name__=='__main__': main()
