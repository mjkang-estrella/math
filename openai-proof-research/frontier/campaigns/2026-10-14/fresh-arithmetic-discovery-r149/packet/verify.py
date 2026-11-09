#!/usr/bin/env python3
"""Read-only artifact verifier. Detached anchors are mandatory; no mathematical gate."""
import argparse, hashlib, json
from pathlib import Path

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--packet',required=True)
    ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--report',required=True)
    ap.add_argument('--report-sha256',required=True)
    ap.add_argument('--working-root')
    ap.add_argument('--project-root')
    a=ap.parse_args(); p=Path(a.packet)
    assert digest(p/'FINAL.md')==a.final_sha256, 'FINAL anchor'
    assert digest(p/'MANIFEST.json')==a.manifest_sha256, 'MANIFEST anchor'
    assert digest(Path(a.report))==a.report_sha256, 'REPORT anchor'
    m=json.loads((p/'MANIFEST.json').read_text())
    expected=set(m['files'])|{'MANIFEST.json'}
    actual={x.relative_to(p).as_posix() for x in p.rglob('*') if x.is_file() or x.is_symlink()}
    assert actual==expected, 'exact member set'
    for rel,v in m['files'].items():
        assert not Path(rel).is_absolute() and '..' not in Path(rel).parts, 'unsafe member'
        q=p/rel; assert not q.is_symlink(), 'symlink'
        assert q.stat().st_size==v['bytes'] and digest(q)==v['sha256'], 'member '+rel
        assert (q.stat().st_mode & 0o777)==v['mode'], 'mode '+rel
        if a.working_root:
            q0=Path(a.working_root)/rel
            assert not q0.is_symlink() and q0.read_bytes()==q.read_bytes(), 'working counterpart '+rel
    canonical=0; originals=0
    if (p/'private/source-bindings.json').exists():
        tree={x['path']:x for x in json.loads((p/'private/source-tree-selected.json').read_text())}
        for v in json.loads((p/'private/source-bindings.json').read_text()):
            q=p/'private/source'/Path(v['local']).name; b=q.read_bytes()
            blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            assert blob==v['git_blob']==tree[v['path']]['sha']
            assert len(b)==v['size']==tree[v['path']]['size'] and digest(q)==v['sha256']
            assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in v['url']
            canonical+=1
        assert canonical==8
    if a.project_root:
        project=Path(a.project_root)
        tree=project/'sources/preprints-tree.json'
        assert tree.stat().st_size==4858136
        assert digest(tree)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
        for v in json.loads((p/'private/completed-bindings.json').read_text()):
            b=(project/v['path']).read_bytes()
            assert hashlib.sha256(b).hexdigest()==v['sha256'] and b==(p/v['local']).read_bytes()
            originals+=1
        for v in json.loads((p/'private/history-extents.json').read_text()):
            with (project/v['path']).open('rb') as f:
                f.seek(v['start']); b=f.read(v['end']-v['start'])
            assert hashlib.sha256(b).hexdigest()==v['sha256']
            assert b==(p/'private'/Path(v['local']).name).read_bytes()
            originals+=1
        for rel in ['AGENTS.md','sources/upstream.json']:
            assert (project/rel).read_bytes()==(p/'private'/rel.replace('/','__')).read_bytes()
        for path,start,end,name in [
            ('frontier/NEW-TEN-2026-10-14.md',4801,6347,'acceptance-4801-6347.txt'),
            ('sources/CONTENTS.md',89640,90608,'source050-catalogue-89640-90608.txt')]:
            with (project/path).open('rb') as f:
                f.seek(start); b=f.read(end-start)
            assert b==(p/'private'/name).read_bytes()
    print(json.dumps({'artifact_match':True,'members':len(m['files']),'canonical_blobs':canonical,'explicit_originals_or_ranges':originals,'mathematical_gate':False}))

if __name__=='__main__':
    main()
