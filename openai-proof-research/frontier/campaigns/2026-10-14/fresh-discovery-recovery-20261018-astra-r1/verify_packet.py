#!/usr/bin/env python3
"""Read-only byte identity verification; the expected anchor must be supplied externally."""
import argparse,hashlib,json,pathlib,sys

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root,exclude):
    out={}
    for p in root.rglob('*'):
        rel=p.relative_to(root)
        if any(rel==e or e in rel.parents for e in exclude):continue
        if p.is_symlink():raise ValueError('symlink:'+str(rel))
        if p.is_file():out[rel.as_posix()]=p
        elif not p.is_dir():raise ValueError('nonregular:'+str(rel))
    return out

def check(root,doc,exclude):
    entries=doc['files'];seen=set()
    for e in entries:
        s=e['path'];p=pathlib.PurePosixPath(s)
        if p.is_absolute() or '..' in p.parts or '.' in p.parts or s!=p.as_posix() or s in seen:raise ValueError('unsafe-or-duplicate-path:'+s)
        seen.add(s)
    actual=inventory(root,exclude)
    if set(actual)!=seen:raise ValueError('inventory-set-mismatch')
    for e in entries:
        p=actual[e['path']]
        if p.stat().st_size!=e['bytes'] or sha(p)!=e['sha256']:raise ValueError('payload-mismatch:'+e['path'])
    return len(entries)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--expected-sha256',required=True);ap.add_argument('--root',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parent);ap.add_argument('--with-private',action='store_true');a=ap.parse_args()
    if len(a.expected_sha256)!=64 or any(c not in '0123456789abcdef' for c in a.expected_sha256):raise ValueError('invalid-anchor-format')
    root=a.root.resolve();m=root/'MANIFEST.json'
    if m.is_symlink() or not m.is_file():raise ValueError('manifest-not-regular')
    if sha(m)!=a.expected_sha256:raise ValueError('external-anchor-mismatch')
    count=check(root,json.loads(m.read_text()),{pathlib.Path('private'),pathlib.Path('MANIFEST.json')})
    result={'status':'IDENTITY_PASS_NOT_MATHEMATICAL_REVIEW','manifest_sha256':sha(m),'public_files':count}
    if a.with_private:
        prov=json.loads((root/'provenance.json').read_text());pm=root/'private'/'INVENTORY.json'
        if pm.is_symlink() or sha(pm)!=prov['private_inventory_sha256']:raise ValueError('private-inventory-anchor-mismatch')
        result['private_files']=check(root/'private',json.loads(pm.read_text()),{pathlib.Path('INVENTORY.json')})
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,OSError,TypeError,json.JSONDecodeError) as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
