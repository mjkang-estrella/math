#!/usr/bin/env python3
"""Read-only packet verifier. Three explicit detached SHA256 anchors are required."""
import argparse, hashlib, json, os, re, stat
from pathlib import Path, PurePosixPath

PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
FAMILY='preprints/The-circulant-Hadamard-conjecture-September-23-2026'
EXACT=[
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162cq-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cq/private/COMPARISON.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cq/WORKLOG.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cq/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cq/FINAL.md']
DETACHED={'MANIFEST.json','REPORT.md'}

def digest(data): return hashlib.sha256(data).hexdigest()
def safe(s):
    assert isinstance(s,str) and s and '\\' not in s and '\x00' not in s
    p=PurePosixPath(s)
    assert not p.is_absolute() and '..' not in p.parts and '.' not in p.parts and str(p)==s
    return s

def inventory(root):
    files={};dirs={'.':root.lstat().st_mode}
    assert stat.S_ISDIR(dirs['.']) and not root.is_symlink()
    def walk(path):
        for e in sorted(os.scandir(path),key=lambda x:x.name):
            s=Path(e.path).relative_to(root).as_posix();safe(s)
            st=e.stat(follow_symlinks=False)
            assert not stat.S_ISLNK(st.st_mode),('symlink',s)
            if stat.S_ISDIR(st.st_mode):dirs[s]=st.st_mode;walk(Path(e.path))
            else:assert stat.S_ISREG(st.st_mode),('nonregular',s);files[s]=st
    walk(root)
    return files,dirs

def core(root,m,require_detached=True):
    assert m['schema']=='r162cr-exact-packet-v1'
    records=m['files'];names=[safe(x['path']) for x in records]
    assert names==sorted(names) and len(names)==len(set(names)),'unsafe/duplicate/unsorted membership'
    assert not (set(names)&DETACHED)
    got,dirs=inventory(root)
    assert set(got)-DETACHED==set(names),'exact file membership'
    drecords=m['directories'];dnames=[x['path'] for x in drecords]
    assert dnames==sorted(dnames) and len(dnames)==len(set(dnames))
    for name in dnames:
        if name!='.':safe(name)
    assert dirs=={x['path']:x['full_mode'] for x in drecords},'exact directories/full modes'
    for rec in records:
        path=root/rec['path'];data=path.read_bytes()
        assert len(data)==rec['bytes'] and digest(data)==rec['sha256'],('bytes/hash',rec['path'])
        assert got[rec['path']].st_mode==rec['full_mode'],('full mode',rec['path'])
    assert set(m['detached_full_modes'])==DETACHED
    for s in DETACHED:
        if require_detached:assert s in got
        if s in got:assert got[s].st_mode==m['detached_full_modes'][s],('detached mode',s)
    return len(records),sum(x['bytes'] for x in records),len(dirs)

def bindings(root,project):
    selected=json.loads((root/'private/source-tree.json').read_text())
    assert len(selected)==13
    assert all(e['path']==FAMILY or e['path'].startswith(FAMILY+'/') for e in selected)
    assert len({e['path'] for e in selected})==len(selected)
    assert sum(e['type']=='tree' for e in selected)==3
    bypath={e['path']:e for e in selected if e['type']=='blob'};assert len(bypath)==10
    records=json.loads((root/'private/source-authentication.json').read_text())
    assert len(records)==10 and {e['path'] for e in records}==set(bypath)
    for rec in records:
        assert rec['url_raw']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+rec['path']
        e=bypath[rec['path']]
        assert (rec['sha'],rec['size'],rec['mode'])==(e['sha'],e['size'],e['mode'])
        data=(root/safe(rec['local'])).read_bytes()
        assert len(data)==e['size'] and digest(data)==rec['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']
    texts=[x for x in records if not x['path'].endswith('.pdf')]
    assert len(texts)==9 and sum(x['size'] for x in texts)==50986
    copies=json.loads((root/'private/completed-bindings.json').read_text())
    assert [x['original'] for x in copies]==EXACT
    for rec in copies:
        original=project/rec['original'];assert stat.S_ISREG(original.lstat().st_mode)
        data=original.read_bytes();copy=root/safe(rec['copy'])
        assert original.stat().st_mode==rec['full_mode'],'original full mode changed'
        assert len(data)==rec['bytes'] and digest(data)==rec['sha256'],'original bytes changed'
        assert copy.read_bytes()==data,'exact completed copy'
        if 'copy_full_mode' in rec:assert copy.stat().st_mode==rec['copy_full_mode'],'copy full mode changed'
    primaries=json.loads((root/'private/primary/bindings.json').read_text())
    assert len(primaries)==8
    for rec in primaries:
        for field,hfield,bfield in [('pdf','sha256','bytes'),('text','text_sha256','text_bytes')]:
            data=(root/safe(rec[field])).read_bytes()
            assert len(data)==rec[bfield] and digest(data)==rec[hfield]
    return {'source_blobs':10,'complete_texts':9,'completed_copies':5,'primary_pdfs':8}

def check(root,anchors,project=None,with_bindings=True):
    for s,key in [('MANIFEST.json','manifest'),('FINAL.md','final'),('REPORT.md','report')]:
        a=anchors[key];assert re.fullmatch('[0-9a-f]{64}',a),'invalid explicit anchor'
        assert digest((root/s).read_bytes())==a,('detached anchor mismatch',key)
    m=json.loads((root/'MANIFEST.json').read_text())
    result=core(root,m)
    bound=bindings(root,project) if with_bindings else None
    return {'status':'MATCH','payload_files':result[0],'payload_bytes':result[1],'directories':result[2],'bindings':bound}

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--root',required=True);a.add_argument('--project-root',required=True)
    for k in ['manifest','final','report']:a.add_argument('--'+k+'-sha256',required=True)
    args=a.parse_args()
    try:
        print(json.dumps(check(Path(args.root).absolute(),{k:getattr(args,k+'_sha256') for k in ['manifest','final','report']},Path(args.project_root).absolute()),sort_keys=True))
    except (AssertionError,ValueError,KeyError,OSError) as e:
        print('REJECT:',e);raise SystemExit(1)
