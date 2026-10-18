#!/usr/bin/env python3
"""Exact-inventory verifier. External --expected anchor is required.
Copyright Myeongjin Kang. SPDX-License-Identifier: MIT
"""
import argparse, hashlib, json, pathlib, tempfile

def sha(data):
    return hashlib.sha256(data).hexdigest()

def inventory(root):
    result=[]
    for p in sorted(root.rglob('*')):
        if p.is_symlink():
            raise ValueError('symlink in payload')
        if p.is_file():
            data=p.read_bytes()
            result.append({'path':p.relative_to(root).as_posix(),'bytes':len(data),'sha256':sha(data)})
    return result

def digest(entries):
    return sha(json.dumps(entries,sort_keys=True,separators=(',',':')).encode())

def verify(root,seal,expected):
    def require(ok,message):
        if not ok: raise ValueError(message)
    require(len(expected)==64 and all(c in '0123456789abcdef' for c in expected), 'invalid anchor')
    require(digest(seal['inventory'])==expected, 'wrong external inventory anchor')
    require(seal['inventory_sha256']==expected, 'seal anchor differs')
    require(inventory(root)==seal['inventory'], 'payload exact inventory mismatch')
    return {'status':'PASS','files':len(seal['inventory']),'inventory_sha256':expected}

def controls():
    out=[]
    with tempfile.TemporaryDirectory(prefix='r23-seal-control-', dir=pathlib.Path(__file__).resolve().parent.parent) as tmp:
        r=pathlib.Path(tmp);(r/'a').write_bytes(b'original')
        entries=inventory(r);anchor=digest(entries);seal={'inventory':entries,'inventory_sha256':anchor}
        verify(r,seal,anchor);out.append({'case':'positive','result':'PASS'})
        def rejected(name,expected=anchor):
            try:verify(r,seal,expected)
            except (AssertionError,ValueError):out.append({'case':name,'result':'EXPECTED_REJECTION'})
            else:raise AssertionError('control accepted: '+name)
        rejected('wrong_external_anchor','0'*64)
        (r/'a').write_bytes(b'changed');rejected('changed_bytes')
        forged_entries=inventory(r)
        forged_seal={'inventory':forged_entries,'inventory_sha256':digest(forged_entries)}
        try:verify(r,forged_seal,anchor)
        except ValueError:out.append({'case':'recomputed_seal_original_external_anchor','result':'EXPECTED_REJECTION'})
        else:raise AssertionError('recomputed seal accepted with original anchor')
        (r/'a').write_bytes(b'original');(r/'extra').write_bytes(b'unlisted');rejected('extra_file')
        (r/'extra').unlink();(r/'link').symlink_to('a');rejected('symlink')
        (r/'link').unlink();(r/'a').unlink();rejected('missing_file')
    return {'status':'PASS','controls':out,'meaning':'integrity only, not a mathematical proof review'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--controls',action='store_true');p.add_argument('--expected');p.add_argument('--payload',type=pathlib.Path);p.add_argument('--seal',type=pathlib.Path);a=p.parse_args()
    if a.controls:print(json.dumps(controls(),indent=2))
    else:
        if not a.expected:p.error('--expected external anchor required')
        root=a.payload or pathlib.Path(__file__).resolve().parent
        sealpath=a.seal or root.parent/'seal.json'
        print(json.dumps(verify(root,json.loads(sealpath.read_text()),a.expected),indent=2))
