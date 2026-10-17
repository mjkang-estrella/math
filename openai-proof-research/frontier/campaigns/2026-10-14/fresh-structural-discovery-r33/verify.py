#!/usr/bin/env python3
"""MIT. Offline, read-only, externally anchored inventory and diagnostics."""
import argparse, hashlib, json, pathlib, subprocess, sys

def sha(b): return hashlib.sha256(b).hexdigest()

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--anchor',required=True); args=ap.parse_args()
    root=pathlib.Path(__file__).resolve().parent
    raw=(root/'manifest.json').read_bytes()
    if sha(raw)!=args.anchor:
        raise SystemExit('FAIL: external manifest anchor mismatch')
    manifest=json.loads(raw)
    actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p.relative_to(root).as_posix()!='manifest.json'}
    assert actual==set(manifest['files']), 'inventory mismatch'
    for name,expected in manifest['files'].items():
        assert sha((root/name).read_bytes())==expected, 'payload mismatch: '+name
    sources=json.loads((root/'source-receipts.json').read_text())
    for entry in sources:
        b=(root/entry['path']).read_bytes()
        assert sha(b)==entry['sha256']
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==entry['git_blob']
        assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in entry['url']
    run=subprocess.run([sys.executable,'-B',str(root/'checks.py')],check=True,capture_output=True,text=True)
    assert json.loads(run.stdout)==json.loads((root/'exact-results.json').read_text())
    print(json.dumps({'status':'PASS_INVENTORY_AND_DIAGNOSTICS','payloads':len(actual),
                      'pinned_blobs':len(sources),'anchor':args.anchor,
                      'limitation':'No mathematical proof or novelty certification.'},sort_keys=True))

if __name__=='__main__': main()
