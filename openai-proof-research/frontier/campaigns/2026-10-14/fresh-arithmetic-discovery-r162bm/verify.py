#!/usr/bin/env python3
"""Read-only packet verifier. Anchors must come from the detached handoff."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

EXACT_INPUTS = {
 'AGENTS.md', 'sources/upstream.json',
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162bl-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bl/private/COMPARISON.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bl/private/WORKING.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bl/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bl/FINAL.md',
}

def sha(b): return hashlib.sha256(b).hexdigest()
def safe(s):
    p=PurePosixPath(s)
    assert isinstance(s,str) and s and not p.is_absolute(), 'unsafe path'
    assert str(p)==s and all(x not in ('','.','..') for x in p.parts), 'noncanonical path'
    assert '\\' not in s, 'backslash path'
    return s

def inspect(root):
    assert stat.S_ISDIR(root.lstat().st_mode), 'root is not real directory'
    files={}; dirs={'.':root.lstat().st_mode}
    for base, ds, fs in os.walk(root, followlinks=False):
        for n in ds:
            p=Path(base)/n; mode=p.lstat().st_mode
            assert stat.S_ISDIR(mode), 'symlink/special directory'
            dirs[p.relative_to(root).as_posix()]=mode
        for n in fs:
            p=Path(base)/n; mode=p.lstat().st_mode
            assert stat.S_ISREG(mode), 'symlink/special file'
            files[p.relative_to(root).as_posix()]=p
    return files,dirs

def check(root, final_anchor, manifest_anchor, report_anchor, project=None):
    files,dirs=inspect(root)
    for name, anchor in [('FINAL.md',final_anchor),('MANIFEST.json',manifest_anchor),('REPORT.md',report_anchor)]:
        assert len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor), 'invalid anchor'
        assert sha(files[name].read_bytes())==anchor, 'detached anchor mismatch: '+name
    m=json.loads(files['MANIFEST.json'].read_bytes()); assert m['version']==1
    records=m['files']; names=[safe(x['path']) for x in records]
    assert names==sorted(names) and len(names)==len(set(names)), 'unsorted/duplicate records'
    assert set(files)==set(names)|{'MANIFEST.json','REPORT.md'}, 'file membership mismatch'
    assert not {'MANIFEST.json','REPORT.md'}&set(names), 'self-reference'
    drecords=m['directories']; dnames=[x['path'] for x in drecords]
    assert dnames==sorted(dnames) and len(dnames)==len(set(dnames)), 'directory record order'
    for n in dnames:
        if n!='.': safe(n)
    assert dirs=={x['path']:x['st_mode'] for x in drecords}, 'directory membership/mode mismatch'
    for x in records:
        p=files[x['path']]; b=p.read_bytes()
        assert len(b)==x['bytes'] and sha(b)==x['sha256'], 'payload mismatch: '+x['path']
        assert p.lstat().st_mode==x['st_mode'], 'file mode mismatch: '+x['path']
    for n in ('MANIFEST.json','REPORT.md'):
        assert files[n].lstat().st_mode==m['control_modes'][n], 'control mode mismatch'
    if m.get('bindings'):
        assert project is not None, 'explicit --project required for original bindings'
        inputs=json.loads(files['private/initial-inputs.json'].read_bytes())
        assert {x['original'] for x in inputs}==EXACT_INPUTS and len(inputs)==7
        for x in inputs:
            p=project/safe(x['original']); b=p.read_bytes(); cp=files[safe(x['copy'])]
            assert p.lstat().st_mode==x['st_mode'] and stat.S_ISREG(p.lstat().st_mode)
            assert len(b)==x['size'] and sha(b)==x['sha256'] and cp.read_bytes()==b, 'original/copy mismatch'
        source=json.loads(files['private/source-authentication.json'].read_bytes())
        tree=json.loads(files['private/source-tree.json'].read_bytes())
        prefix='preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/'
        expected={x['path'][len(prefix):]:x for x in tree if x['type']=='blob'}
        assert len(source)==12 and len(tree)==16 and len(expected)==12
        seen=set()
        for x in source:
            name=safe(x['path']); assert name.startswith('private/source/')
            rel=name[len('private/source/'):]; assert rel not in seen; seen.add(rel)
            b=files[name].read_bytes(); t=expected[rel]
            blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            assert len(b)==x['bytes']==t['size'] and blob==x['git_blob']==t['sha']
            assert sha(b)==x['sha256'] and files[name].lstat().st_mode==x['st_mode']
            assert t['mode']=='100644'
        assert seen==set(expected)
        assert sha(files['STATEMENT.md'].read_bytes())=='6f1c7eed54c4bee7b80a56494fddfb0e5e0bcd66f0e4b9acc2a2fdb6458f5127'
    return {'payloads':len(records),'files':len(files),'directories_including_root':len(dirs),
            'payload_bytes':sum(x['bytes'] for x in records),'bindings':bool(m.get('bindings'))}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    for n in ['root','final-sha','manifest-sha','report-sha']: p.add_argument('--'+n,required=True)
    p.add_argument('--project')
    a=p.parse_args()
    result=check(Path(a.root),a.final_sha,a.manifest_sha,a.report_sha,Path(a.project) if a.project else None)
    print('MATCH '+json.dumps(result,sort_keys=True))
