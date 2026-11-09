#!/usr/bin/env python3
"""Read-only artifact verification. No mathematical verdict is assigned."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

MNAME='private/MANIFEST.json'
RNAME='REPORT.md'
TYPES=stat.S_IFREG|0o644

def digest(b): return hashlib.sha256(b).hexdigest()
def safe(s):
    p=PurePosixPath(s)
    assert s and not p.is_absolute() and str(p)==s and all(x not in ('','.','..') for x in p.parts), ('unsafe',s)
    return s

def inventory(root):
    files={}; dirs={'.':root.stat().st_mode}
    assert not root.is_symlink() and stat.S_ISDIR(root.stat().st_mode)
    for d,ds,fs in os.walk(root,followlinks=False):
        for n in ds:
            p=Path(d)/n; assert not p.is_symlink();s=p.relative_to(root).as_posix();safe(s)
            assert stat.S_ISDIR(p.stat().st_mode);dirs[s]=p.stat().st_mode
        for n in fs:
            p=Path(d)/n;assert not p.is_symlink();s=p.relative_to(root).as_posix();safe(s)
            assert stat.S_ISREG(p.stat().st_mode);files[s]=p.stat().st_mode
    return files,dirs

def check_records(root,records,expected_dirs,virtual=None):
    virtual=virtual or {};files,dirs=inventory(root)
    for s,(b,mode) in virtual.items():
        safe(s);assert s not in files;files[s]=mode
    names=[safe(x['path']) for x in records]
    assert names==sorted(names) and len(names)==len(set(names)), 'records not sorted unique'
    assert set(files)==set(names), ('membership',sorted(set(files)^set(names)))
    assert dirs==expected_dirs, 'directory modes/membership'
    for x in records:
        s=x['path'];b=virtual[s][0] if s in virtual else (root/s).read_bytes()
        assert files[s]==x['mode'],('mode',s)
        assert len(b)==x['bytes'] and digest(b)==x['sha256'],('bytes/hash',s)
    return sum(x['bytes'] for x in records)

def bindings(root,project):
    # Only the exact direct tree path and the five explicitly listed originals are read.
    raw=(project/'sources/preprints-tree.json').read_bytes()
    assert len(raw)==4858136 and digest(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    all_es=json.loads(raw)['tree'];assert len(all_es)==13223
    es=json.loads((root/'private/source-tree.json').read_bytes());assert len(es)==20
    tops=[x['path'] for x in es if x['type']=='tree' and '/' not in x['path'].removeprefix('preprints/')]
    assert len(tops)==1;top=tops[0]
    assert es==[x for x in all_es if x['path']==top or x['path'].startswith(top+'/')]
    blob_count=0;tree_count=0
    for e in es:
        if e['type']=='blob':
            p=root/'private/source'/e['path'][len(top)+1:];b=p.read_bytes()
            assert len(b)==e['size']
            assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']
            assert (p.stat().st_mode & 0o777)==(int(e['mode'],8)&0o777)
            blob_count+=1
        else:
            prefix=e['path']+'/'
            children=[x for x in es if x['path'].startswith(prefix) and '/' not in x['path'][len(prefix):]]
            children.sort(key=lambda x:(x['path'][len(prefix):]+('/' if x['type']=='tree' else '')).encode())
            b=b''.join(x['mode'].lstrip('0').encode()+b' '+x['path'][len(prefix):].encode()+b'\0'+bytes.fromhex(x['sha']) for x in children)
            assert hashlib.sha1(b'tree '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']
            tree_count+=1
    sb=json.loads((root/'private/source-bindings.json').read_bytes())
    assert sb['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    assert len(sb['records'])==blob_count
    for path,n,h in sb['records']:
        b=(root/'private/source'/path[len(top)+1:]).read_bytes();assert len(b)==n and digest(b)==h
    copies=json.loads((root/'private/completed-bindings.json').read_bytes());assert len(copies)==5
    assert len({x['original'] for x in copies})==5
    for x in copies:
        safe(x['original']);safe(x['copy']);o=project/x['original'];c=root/x['copy']
        assert not o.is_symlink() and not c.is_symlink()
        b=o.read_bytes();assert b==c.read_bytes() and len(b)==x['bytes'] and digest(b)==x['sha256']
        assert o.stat().st_mode==x['original_full_mode_preseal'] and c.stat().st_mode==x['copy_full_mode_preseal']
        assert stat.S_IMODE(o.stat().st_mode)==x['mode']
    prim=json.loads((root/'private/primary/bindings.json').read_bytes());pc=0
    for x in prim:
        if 'error' in x:continue
        b=(root/'private/primary'/(x['id']+'.pdf')).read_bytes()
        assert len(b)==x['bytes'] and digest(b)==x['sha256'];pc+=1
    return {'source_blobs':blob_count,'source_trees':tree_count,'completed_pairs':len(copies),'primary_pdfs':pc}

def verify(root,project,anchors,virtual=None):
    virtual=virtual or {}
    def read(s):return virtual[s][0] if s in virtual else (root/s).read_bytes()
    for s,h in zip(['FINAL.md',MNAME,RNAME],anchors):assert len(h)==64 and digest(read(s))==h,('detached anchor',s)
    m=json.loads(read(MNAME));assert m['schema']=='r162by-artifact-v1'
    assert m['exclusions']==[MNAME,RNAME]
    rs=m['files']+ [{'path':s,'bytes':len(read(s)),'sha256':digest(read(s)),'mode':TYPES} for s in [MNAME,RNAME]]
    rs.sort(key=lambda x:x['path'])
    n=check_records(root,rs,m['directories'],virtual)
    report=read(RNAME).decode();assert anchors[0] in report and anchors[1] in report
    bound=bindings(root,project)
    return dict(payloads=len(m['files']),files=len(rs),directories=len(m['directories']),payload_bytes=sum(x['bytes'] for x in m['files']),whole_bytes=n,**bound)

def main():
    a=argparse.ArgumentParser();a.add_argument('--final',required=True);a.add_argument('--manifest',required=True);a.add_argument('--report',required=True)
    x=a.parse_args();root=Path(__file__).resolve().parent;project=root.parents[3]
    print('MATCH '+json.dumps(verify(root,project,[x.final,x.manifest,x.report]),sort_keys=True))
if __name__=='__main__':main()
