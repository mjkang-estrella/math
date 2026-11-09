#!/usr/bin/env python3
"""Read-only R162BX verifier. Explicit detached anchors are mandatory."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PROJECT = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
ROOT_REL = 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bx'
META = {'MANIFEST.json', 'REPORT.md'}
PREFIXES = (
 'preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026',
 'preprints/A-counterexample-to-the-Colin-de-Verdiere-chromatic-conjecture-September-23-2026',
 'preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026',
)
COMPLETED = {
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162bw-parent/assessment.md': 'private/completed/01-assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bw/private/DERIVATION.md': 'private/completed/02-DERIVATION.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bw/WORKING.md': 'private/completed/03-WORKING.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bw/private/READING-LIMITS.md': 'private/completed/04-READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bw/FINAL.md': 'private/completed/05-FINAL.md',
}
PRIMARY_IDS = {'bernshteyn2016','delcourt-postle-v5','postle2020','fractional-dp','reed-seymour','dvorak-postle','girao-narayanan','dvorak-yepremyan'}

def sha(b):
    return hashlib.sha256(b).hexdigest()

def safe(name):
    assert isinstance(name, str) and name and '\\' not in name
    p = PurePosixPath(name)
    assert not p.is_absolute() and all(x not in ('', '.', '..') for x in p.parts)
    assert p.as_posix() == name
    return name

def inventory(root, exclusions=frozenset()):
    root = Path(root)
    assert stat.S_ISDIR(root.lstat().st_mode)
    files, dirs = [], []
    def descend(p):
        for q in sorted(p.iterdir(), key=lambda v:v.name):
            rel = q.relative_to(root).as_posix()
            safe(rel)
            st = q.lstat()
            assert not stat.S_ISLNK(st.st_mode), ('symlink',rel)
            if rel in exclusions:
                assert stat.S_ISREG(st.st_mode), ('nonregular metadata',rel)
                continue
            if stat.S_ISDIR(st.st_mode):
                dirs.append({'path':rel, 'mode':st.st_mode})
                descend(q)
            else:
                assert stat.S_ISREG(st.st_mode), ('special file',rel)
                b=q.read_bytes()
                files.append({'path':rel, 'bytes':len(b), 'sha256':sha(b), 'mode':st.st_mode})
    descend(root)
    return {'root_mode':root.lstat().st_mode,
            'directories':sorted(dirs,key=lambda x:x['path']),
            'files':sorted(files,key=lambda x:x['path'])}

def verify_inventory(root, manifest, exclusions=frozenset()):
    for kind in ('files','directories'):
        names=[safe(e['path']) for e in manifest[kind]]
        assert names==sorted(names) and len(names)==len(set(names)), ('order/duplicates',kind)
        assert not (set(names)&set(exclusions))
    actual=inventory(root,exclusions)
    assert actual['root_mode']==manifest['root_mode'], 'root full mode'
    assert actual['directories']==manifest['directories'], 'directory membership/full modes'
    assert actual['files']==manifest['files'], 'file membership/bytes/hash/full modes'
    return actual

def verify_bindings(root):
    p=root/'private'
    tree=json.loads((p/'source-tree.json').read_text())
    assert len(tree)==72
    paths=[safe(e['path']) for e in tree]
    assert len(paths)==len(set(paths))
    assert all(any(s==a or s.startswith(a+'/') for a in PREFIXES) for s in paths)
    entries={e['path']:e for e in tree}
    blobs={e['path']:e for e in tree if e['type']=='blob'}
    assert len(blobs)==60
    bnd=json.loads((p/'canonical-bindings.json').read_text())
    assert len(bnd)==60 and {x['path'] for x in bnd}==set(blobs)
    assert len({x['path'] for x in bnd})==60
    canonical=p/'canonical'
    observed={e['path'] for e in inventory(canonical)['files']}
    assert observed==set(blobs), 'exact canonical membership'
    total=0
    for e in bnd:
        name=safe(e['path']); md=blobs[name]; f=canonical/name; data=f.read_bytes()
        assert e['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+name
        assert len(data)==md['size']==e['bytes']
        assert sha(data)==e['sha256']
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert blob==md['sha']==e['git_blob'], ('Git binding',name)
        assert f.lstat().st_mode==int(md['mode'],8), ('source full mode',name)
        total+=len(data)
    assert total==3633729
    assert sum(e['size'] for e in blobs.values() if not e['path'].lower().endswith('.pdf'))==995207
    copies=json.loads((p/'completed-bindings.json').read_text())
    assert len(copies)==5 and {e['original']:e['copy'] for e in copies}==COMPLETED
    for e in copies:
        orig=PROJECT/e['original']; cp=root/e['copy']
        assert stat.S_ISREG(orig.lstat().st_mode) and stat.S_ISREG(cp.lstat().st_mode)
        x,y=orig.read_bytes(),cp.read_bytes()
        assert x==y and len(x)==e['bytes'] and sha(x)==e['sha256']
        assert stat.S_IMODE(orig.lstat().st_mode)==e['mode']
        assert orig.lstat().st_mode==e['comparison_original_full_mode']
        assert cp.lstat().st_mode==e['comparison_copy_full_mode']
    prim=json.loads((p/'primary-bindings.json').read_text())
    ok=[e for e in prim if 'error' not in e]
    assert len(ok)==8 and {e['id'] for e in ok}==PRIMARY_IDS
    for e in ok:
        data=(p/'primaries'/(e['id']+'.pdf')).read_bytes()
        assert len(data)==e['bytes'] and sha(data)==e['sha256']
    assert (p/'controls/original.txt').read_bytes()==(p/'controls/fixture/sample.txt').read_bytes()
    return {'canonical_blobs':60,'canonical_bytes':total,'completed_copies':5,'primary_pdfs':8}

def verify_packet(root, manifest_bytes, report_bytes, final_anchor, manifest_anchor, report_anchor):
    for h in (final_anchor,manifest_anchor,report_anchor):
        assert re.fullmatch('[0-9a-f]{64}',h), 'invalid detached anchor'
    assert sha(manifest_bytes)==manifest_anchor, 'MANIFEST detached anchor'
    assert sha(report_bytes)==report_anchor, 'REPORT detached anchor'
    manifest=json.loads(manifest_bytes)
    assert manifest['schema']=='r162bx-seal-v1' and manifest['pin']==PIN
    actual=verify_inventory(root,manifest,META)
    assert sha((root/'FINAL.md').read_bytes())==final_anchor, 'FINAL detached anchor'
    report=report_bytes.decode('utf-8')
    assert 'FINAL_SHA256 '+final_anchor in report
    assert 'MANIFEST_SHA256 '+manifest_anchor in report
    bindings=verify_bindings(root)
    return dict(payload_files=len(actual['files']),whole_root_files=len(actual['files'])+2,
                directories_including_root=len(actual['directories'])+1,
                payload_bytes=sum(e['bytes'] for e in actual['files']),**bindings)

def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('--final',required=True)
    a.add_argument('--manifest',required=True)
    a.add_argument('--report',required=True)
    o=a.parse_args()
    root=Path(__file__).resolve().parent
    assert root==PROJECT/ROOT_REL
    for name in META:
        assert (root/name).lstat().st_mode==0o100644, ('metadata full mode',name)
    result=verify_packet(root,(root/'MANIFEST.json').read_bytes(),(root/'REPORT.md').read_bytes(),o.final,o.manifest,o.report)
    print('MATCH '+json.dumps(result,sort_keys=True))

if __name__=='__main__':
    main()
