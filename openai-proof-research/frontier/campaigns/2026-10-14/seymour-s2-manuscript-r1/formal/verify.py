#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT. File identity only, not mathematical proof."""
import hashlib
import json
from pathlib import Path


def main():
    root=Path(__file__).resolve().parent
    data=json.loads((root/'output-manifest.json').read_text())
    for entry in data['files']:
        target=(root/entry['path']).resolve()
        if not target.is_relative_to(root) or not target.is_file():
            raise ValueError('Missing or escaping manifest path: '+entry['path'])
        raw=target.read_bytes()
        if len(raw)!=entry['bytes'] or hashlib.sha256(raw).hexdigest()!=entry['sha256']:
            raise ValueError('File changed: '+entry['path'])
    print(json.dumps({'status':'PASS file identity only','files':len(data['files']),
                      'full_S2_formalized':False,'independent_audit':False}))

if __name__=='__main__':main()
