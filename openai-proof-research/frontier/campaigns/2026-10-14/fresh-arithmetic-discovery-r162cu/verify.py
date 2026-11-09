#!/usr/bin/env python3
"""Read-only artifact verifier. Explicit detached anchors; no mathematical gates."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
MANIFEST = 'private/MANIFEST.json'
EXCLUDED = {MANIFEST, 'REPORT.md'}
EXCEPTIONS = (
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162ct-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct/private/COMPARISON.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct/WORKLOG.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct/FINAL.md',
)
FAMILIES = (
 'preprints/A-Power-Saving-for-Polynomial-Differences-at-Prime-Arguments-October-5-2026',
 'preprints/A-power-saving-for-intersective-polynomial-differences-with-an-exponent-depending-only-on-the-degree-October-5-2026',
 'preprints/A-power-saving-for-square-difference-free-sets-September-24-2026',
)
COMPANION = 'preprints/The-Quasi-Riemann-Hypothesis-September-30-2026'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def safe(s):
    assert isinstance(s, str) and s and '\\' not in s and '\0' not in s
    p = PurePosixPath(s)
    assert not p.is_absolute() and str(p) == s
    assert all(x not in ('', '.', '..') for x in p.parts)
    return s

def collect(root):
    root = Path(root)
    assert stat.S_ISDIR(root.lstat().st_mode) and not root.is_symlink()
    files, dirs = [], [{'path': '.', 'full_mode': root.lstat().st_mode}]
    def visit(d):
        for e in sorted(os.scandir(d), key=lambda x:x.name):
            p = Path(e.path); rel = safe(p.relative_to(root).as_posix())
            st = e.stat(follow_symlinks=False)
            assert not stat.S_ISLNK(st.st_mode), 'symlink: '+rel
            if stat.S_ISDIR(st.st_mode):
                dirs.append({'path':rel, 'full_mode':st.st_mode}); visit(p)
            else:
                assert stat.S_ISREG(st.st_mode) and st.st_nlink == 1, 'nonregular/linked: '+rel
                if rel not in EXCLUDED:
                    b=p.read_bytes()
                    files.append({'path':rel, 'bytes':len(b), 'sha256':sha(b), 'full_mode':st.st_mode})
    visit(root)
    return sorted(files,key=lambda x:x['path']), sorted(dirs,key=lambda x:x['path'])

def bindings(root, project):
    tree_b=(root/'private/tree.json').read_bytes()
    assert sha(tree_b)==TREE_SHA and len(tree_b)==4858136
    tree=json.loads(tree_b)
    assert tree.get('truncated') is False and len(tree['tree'])==13223
    entries={e['path']:e for e in tree['tree']}
    assert len(entries)==13223
    records=[]
    for fn,prefixes,count in [('source-bindings.json',FAMILIES,40),('companion-bindings.json',(COMPANION,),3)]:
        rr=json.loads((root/'private'/fn).read_bytes()); assert len(rr)==count
        expected={p for p,e in entries.items() if e['type']=='blob' and any(p.startswith(q+'/') for q in prefixes)}
        assert {r['path'] for r in rr}==expected and len(expected)==len(rr)
        for r in rr:
            e=entries[r['path']]; copy=safe(r['copy'])
            assert copy=='private/source/'+r['path']
            assert r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path']
            p=root/copy; b=p.read_bytes()
            assert len(b)==r['bytes']==e['size'] and sha(b)==r['sha256']
            blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            assert blob==r['git']==e['sha']
            assert p.lstat().st_mode==int(e['mode'],8)
        records.extend(rr)
    selected=[e for e in tree['tree'] if any(e['path']==q or e['path'].startswith(q+'/') for q in FAMILIES)]
    recorded=json.loads((root/'private/source-entries.json').read_bytes())
    assert len(selected)==54 and sorted(selected,key=lambda e:e['path'])==sorted(recorded,key=lambda e:e['path'])
    rr=json.loads((root/'private/exceptions.json').read_bytes())
    assert len(rr)==5 and {r['path'] for r in rr}==set(EXCEPTIONS)
    for r in rr:
        original=project/r['path']; copy=root/safe(r['copy'])
        assert stat.S_ISREG(original.lstat().st_mode) and not original.is_symlink()
        assert original.lstat().st_mode==r['full_mode']==copy.lstat().st_mode
        assert stat.S_IMODE(original.lstat().st_mode)==r['mode']
        b=original.read_bytes(); assert b==copy.read_bytes()
        assert len(b)==r['bytes'] and sha(b)==r['sha256']
    for name,start,end,copy in [
        ('frontier/NEW-TEN-2026-10-14.md',4801,6347,'private/journal-window.txt'),
        ('sources/CONTENTS.md',284310,287105,'private/catalogue-window.txt')]:
        with (project/name).open('rb') as f:
            f.seek(start); b=f.read(end-start)
        assert len(b)==end-start and b==(root/copy).read_bytes()
    return len(records)

def verify_packet(root, anchors, project=None, provisional_manifest=None, fixture=False):
    root=Path(root)
    for key in ('final','manifest','report'):
        value=anchors[key]
        assert len(value)==64 and all(c in '0123456789abcdef' for c in value), 'bad anchor syntax'
    assert sha((root/'FINAL.md').read_bytes())==anchors['final'], 'FINAL anchor mismatch'
    assert sha((root/'REPORT.md').read_bytes())==anchors['report'], 'REPORT anchor mismatch'
    mb=(root/MANIFEST).read_bytes() if provisional_manifest is None else provisional_manifest
    assert sha(mb)==anchors['manifest'], 'MANIFEST anchor mismatch'
    m=json.loads(mb)
    assert m['schema']==1 and m['kind']==('tiny-control' if fixture else 'r162cu-author-packet')
    for key in ('files','directories'):
        paths=[r['path'] for r in m[key]]
        assert paths==sorted(paths) and len(paths)==len(set(paths)), 'unsorted/duplicate membership'
        for p in paths:
            if key=='directories' and p=='.':continue
            safe(p)
    assert not any(r['path'] in EXCLUDED for r in m['files'])
    files,dirs=collect(root)
    assert files==m['files'], 'file membership/hash/length/full-mode mismatch'
    assert dirs==m['directories'], 'directory membership/full-mode mismatch'
    assert set(m['detached_modes'])==EXCLUDED
    for name,mode in m['detached_modes'].items():
        if name==MANIFEST and provisional_manifest is not None and not (root/name).exists():continue
        assert (root/name).lstat().st_mode==mode, 'detached mode mismatch'
    bound=0
    if not fixture:
        assert m['source_pin']==PIN and m['complete_tree_sha256']==TREE_SHA
        assert project is not None
        bound=bindings(root,Path(project))
    return {'payload_files':len(files),'directories_including_root':len(dirs),'payload_bytes':sum(f['bytes'] for f in files),'pinned_blobs':bound}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',required=True)
    p.add_argument('--project')
    p.add_argument('--final',required=True)
    p.add_argument('--manifest',required=True)
    p.add_argument('--report',required=True)
    p.add_argument('--fixture',action='store_true')
    a=p.parse_args()
    try:
        result=verify_packet(a.root,{'final':a.final,'manifest':a.manifest,'report':a.report},project=a.project,fixture=a.fixture)
    except Exception as e:
        print('REJECT',type(e).__name__,str(e));raise SystemExit(1)
    print('MATCH',json.dumps(result,sort_keys=True))
