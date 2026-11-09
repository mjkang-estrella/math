#!/usr/bin/env python3
"""Read-only exact-anchor integrity verifier; not a mathematical gate."""
import argparse, hashlib, json, stat
from pathlib import Path, PurePosixPath
PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
ROOT=PROJECT/'frontier/campaigns/2026-10-14/arithmetic-r162aj-contribution-r1'

def named(base,name):
    p=PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts: raise ValueError('unsafe relative path')
    out=base.joinpath(*p.parts)
    for q in (out,*out.parents):
        if q==PROJECT.parent: break
        if q.is_symlink(): raise ValueError('symlink denied: '+str(q))
    return out

def digest(b): return hashlib.sha256(b).hexdigest()
def anchored(path,anchor):
    if len(anchor)!=64 or any(c not in '0123456789abcdef' for c in anchor):
        raise ValueError('an explicit lowercase SHA256 anchor is required')
    data=path.read_bytes()
    if digest(data)!=anchor: raise ValueError('anchor mismatch: '+str(path))
    return data

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--final',required=True)
    p.add_argument('--manifest',required=True)
    p.add_argument('--report',required=True)
    p.add_argument('--inputs',action='store_true',help='also check exactly selected readonly inputs; journal uses seek/read of its extent only')
    a=p.parse_args()
    if Path.cwd()!=PROJECT: raise ValueError('run with the required project workdir')
    anchored(named(ROOT,'FINAL.md'),a.final)
    anchored(named(ROOT,'REPORT.md'),a.report)
    manifest=json.loads(anchored(named(ROOT,'MANIFEST.json'),a.manifest))
    seen=set()
    for x in manifest['files']:
        if x['path'] in seen: raise ValueError('duplicate payload entry')
        seen.add(x['path']);q=named(ROOT,x['path'])
        b=anchored(q,x['sha256'])
        if len(b)!=x['bytes'] or stat.S_IMODE(q.stat().st_mode)!=x['mode']:
            raise ValueError('size/mode mismatch: '+str(q))
    c=json.loads(named(ROOT,'private/CONTROL-RESULTS.json').read_bytes())
    anchored(named(ROOT,c['matching_copy']),c['expected_sha256'])
    if digest(named(ROOT,c['changed_copy']).read_bytes())==c['expected_sha256']:
        raise ValueError('negative copied control did not differ')
    n=0
    if a.inputs:
        for x in json.loads(named(ROOT,'private/inputs.json').read_bytes())['items']:
            q=named(PROJECT,x['path'])
            if 'extent_half_open' in x:
                lo,hi=x['extent_half_open']
                if x['path']!='frontier/NEW-TEN-2026-10-14.md' or [lo,hi]!=[4801,6347]:
                    raise ValueError('unadmitted bounded input')
                with q.open('rb') as f:f.seek(lo);b=f.read(hi-lo)
                if len(b)!=x['extent_bytes'] or digest(b)!=x['extent_sha256']:
                    raise ValueError('bounded input mismatch')
            else:
                b=anchored(q,x['sha256'])
                if len(b)!=x['bytes'] or stat.S_IMODE(q.stat().st_mode)!=x['mode']:
                    raise ValueError('input size/mode mismatch: '+str(q))
                if 'git_blob' in x:
                    blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
                    if blob!=x['git_blob']:raise ValueError('input Git blob mismatch')
            n+=1
    print(json.dumps({'integrity':'matched explicit anchors and exact payload','payload_files':len(seen),'input_objects_checked':n,'copied_controls':'matching and changed copies distinguished','mathematical_gate':False}))

if __name__=='__main__':
    try:main()
    except (OSError,ValueError,KeyError) as e:
        raise SystemExit('INTEGRITY ERROR: '+str(e))
