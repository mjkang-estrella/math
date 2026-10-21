#!/usr/bin/env python3
"""Read-only exact packet check; three external SHA256 values are mandatory."""
import argparse,hashlib,json,os,re
from pathlib import Path

OUTER={'FINAL.md','REPORT.md','MANIFEST.json','ANCHORS.sha256'}
SCHEMA='t185r144-contribution-r1-exact-v1'
FORBIDDEN=re.compile(r'analytic.*r13[5-8]|arithmetic.*r10[7-9]|structural.*r14[34]|t185r144-(?!contribution-r1(?:$|/))|t177c143-|t373e135-|k369r134-|t088p133-',re.I)

def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()

def safe(s):
    p=Path(s)
    if not s or p.is_absolute() or '..' in p.parts or str(p)!=s or any(FORBIDDEN.search(c) for c in p.parts):
        raise ValueError('Unsafe/excluded relative path: '+s)

def inventory(root):
    fs=set();ds=set()
    for base,dirs,files in os.walk(root,topdown=True,followlinks=False):
        for n in list(dirs):
            p=Path(base)/n;s=p.relative_to(root).as_posix();safe(s)
            if p.is_symlink(): dirs.remove(n);raise ValueError('Symlink directory: '+s)
            ds.add(s)
        for n in files:
            p=Path(base)/n;s=p.relative_to(root).as_posix();safe(s)
            if p.is_symlink() or not p.is_file(): raise ValueError('Not regular: '+s)
            fs.add(s)
    return fs,ds

def verify(root,anchors):
    for n,h in anchors.items():
        if not re.fullmatch(r'[0-9a-f]{64}',h): raise ValueError('Malformed detached anchor')
        p=root/n
        if p.is_symlink() or not p.is_file() or digest(p)!=h: raise ValueError('Detached anchor mismatch: '+n)
    m=json.loads((root/'MANIFEST.json').read_text())
    if m['schema']!=SCHEMA or set(m['outer_files'])!=OUTER: raise ValueError('Schema/outer membership')
    names=[e['path'] for e in m['files']]
    if len(names)!=len(set(names)): raise ValueError('Duplicate file')
    for n in names:
        safe(n)
        if n in OUTER: raise ValueError('Outer file in payload')
    if len(m['directories'])!=len(set(m['directories'])): raise ValueError('Duplicate directory')
    for n in m['directories']: safe(n)
    fs,ds=inventory(root)
    if fs!=set(names)|OUTER: raise ValueError('Exact file membership differs')
    if ds!=set(m['directories']): raise ValueError('Exact directory membership differs')
    for e in m['files']:
        p=root/e['path']
        if p.stat().st_size!=e['bytes'] or digest(p)!=e['sha256']: raise ValueError('Payload differs: '+e['path'])
    wanted=''.join(anchors[n]+'  '+n+'\n' for n in ['MANIFEST.json','FINAL.md','REPORT.md'])
    if (root/'ANCHORS.sha256').read_text()!=wanted: raise ValueError('Local anchors differ from supplied external values')

def main():
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('root',type=Path)
    for n in ['manifest','final','report']: a.add_argument('--'+n+'-sha256',required=True)
    args=a.parse_args();verify(args.root.resolve(),{'MANIFEST.json':args.manifest_sha256,'FINAL.md':args.final_sha256,'REPORT.md':args.report_sha256})
    print('Exact bytes/membership verified; no mathematical or historical isolation gate.')

if __name__=='__main__': main()
