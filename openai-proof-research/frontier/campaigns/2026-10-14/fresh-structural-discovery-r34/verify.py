#!/usr/bin/env python3
"""MIT. Read-only inventory verification; no mathematical certification."""
import argparse
import hashlib
import json
import pathlib
import subprocess
import sys

def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--anchor',required=True)
    args=ap.parse_args()
    root=pathlib.Path(__file__).resolve().parent
    raw=(root/'manifest.json').read_bytes()
    if sha(raw)!=args.anchor:
        raise SystemExit('FAIL: external manifest anchor mismatch')
    manifest=json.loads(raw)
    actual={p.relative_to(root).as_posix() for p in root.rglob('*')
            if p.is_file() and p.relative_to(root).as_posix()!='manifest.json'}
    assert actual==set(manifest['files']), 'inventory mismatch'
    for name,digest in manifest['files'].items():
        assert sha((root/name).read_bytes())==digest, 'payload mismatch: '+name
    sources=json.loads((root/'source-receipts.json').read_text())
    for e in sources:
        body=(root/e['path']).read_bytes()
        assert sha(body)==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(body)).encode()+b'\0'+body).hexdigest()==e['git_blob']
        assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in e['url']
    for e in json.loads((root/'primary-receipts.json').read_text()):
        body=(root/e['file']).read_bytes()
        assert len(body)==e['bytes'] and sha(body)==e['sha256']
    for e in json.loads((root/'context-receipts.json').read_text()):
        assert sha((root/e['copy']).read_bytes())==e['sha256']
    run=subprocess.run([sys.executable,'-B',str(root/'checks.py')],check=True,capture_output=True,text=True)
    assert json.loads(run.stdout)==json.loads((root/'exact-results.json').read_text())
    print(json.dumps({'status':'PASS_INVENTORY_AND_DIAGNOSTICS','payloads':len(actual),
                      'pinned_blobs':len(sources),'anchor':args.anchor,
                      'limitation':'Full target unresolved. No mathematical or novelty certification.'},sort_keys=True))

if __name__=='__main__':
    main()
