#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Create a manifest only for this assigned support directory; prints external digest.
Do not reseal an already handed-off packet. Review requires the external digest.
"""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent

def manifest(root):
    rows=[];dirs=[]
    for p in sorted(root.rglob('*')):
        if p.is_symlink(): raise ValueError('symlink')
        r=p.relative_to(root).as_posix()
        if p.is_dir(): dirs.append(r)
        elif p.is_file() and r!='output-manifest.json':
            raw=p.read_bytes();rows.append({'path':r,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
    return {'schema':'CM275-scoped-formal-v1','author':'Myeongjin Kang','affiliation':None,
      'full_CM275_theorem_formalized':False,'independent_formal_verdict':False,
      'candidate_sha256':'b467f8b7797ed4c49c4de799399cffab0bc22629b61a0b214ddf2401e8289ffd',
      'scope_sha256':'5fe6692d799dd949cfdcd87700a3dd9566acdfa5496080991c0e3d9ccad7fd9f',
      'source_pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','files':rows,'directories':dirs}

if __name__=='__main__':
    path=HERE/'output-manifest.json'
    if path.exists(): raise ValueError('Refusing to overwrite an existing seal')
    raw=(json.dumps(manifest(HERE),indent=2,ensure_ascii=False)+'\n').encode()
    path.write_bytes(raw)
    print(hashlib.sha256(raw).hexdigest())
