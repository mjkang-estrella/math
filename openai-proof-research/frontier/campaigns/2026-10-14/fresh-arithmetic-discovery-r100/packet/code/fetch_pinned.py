#!/usr/bin/env python3
"""Author-side fetch script for arithmetic r100. NOT part of verification.

Reproduces the retained pinned sources: downloads each retained upstream path
from the pinned raw URL, checks the git blob SHA-1 and SHA-256 against
public/source-register.json, and writes private/upstream/<path>. Removed
sources are receipts only and are not re-fetched. Requires network access.
"""
import hashlib, json, sys, urllib.request
from pathlib import Path

R = Path(__file__).resolve().parent.parent.parent
reg = json.loads((R / 'packet/public/source-register.json').read_text())


def git_blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def main():
    ok = True
    for x in reg['retained']:
        with urllib.request.urlopen(x['raw_url'], timeout=60) as r:
            b = r.read()
        good = (len(b) == x['size'] and git_blob(b) == x['git_blob']
                and hashlib.sha256(b).hexdigest() == x['sha256'])
        ok &= good
        print(('MATCH ' if good else 'MISMATCH ') + x['upstream_path'])
        if good:
            dest = R / 'packet' / x['local']
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(b)
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
