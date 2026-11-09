#!/usr/bin/env python3
"""Read-only exact-membership verifier; detached anchors MUST be supplied."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

DETACHED = {'MANIFEST.json', 'REPORT.md'}
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def sha(b): return hashlib.sha256(b).hexdigest()
def safe(p):
    q = PurePosixPath(p)
    return p == '.' or (not q.is_absolute() and str(q) == p and '..' not in q.parts and '\\' not in p)
def inventory(root):
    root = Path(root)
    assert not root.is_symlink() and root.is_dir(), 'unsafe root'
    out = [{'path': '.', 'kind': 'dir', 'full_mode': root.lstat().st_mode}]
    for base, dirs, files in os.walk(root, followlinks=False):
        for name in sorted(dirs + files):
            p = Path(base)/name
            rel = p.relative_to(root).as_posix()
            assert safe(rel) and not p.is_symlink(), 'unsafe member'
            if rel in DETACHED: continue
            mode = p.lstat().st_mode
            if stat.S_ISDIR(mode): out.append({'path':rel,'kind':'dir','full_mode':mode})
            else:
                assert stat.S_ISREG(mode), 'nonregular member'
                b = p.read_bytes()
                out.append({'path':rel,'kind':'file','full_mode':mode,'bytes':len(b),'sha256':sha(b)})
    return sorted(out,key=lambda x:x['path'])
def check_inventory(root, manifest):
    records = manifest['records']
    paths = [x['path'] for x in records]
    assert paths == sorted(set(paths)) and all(map(safe,paths)), 'unsafe/order/duplicate manifest'
    assert not set(paths)&DETACHED, 'detached anchor in payload'
    assert records == inventory(root), 'membership/hash/length/full-mode mismatch'
    return records

def check_bindings(root, project):
    root, project = Path(root), Path(project)
    bindings=json.loads((root/'private/source-bindings.json').read_text())
    tree=json.loads((root/'private/source-tree.json').read_text())
    entries={x['path']:x for x in tree if x['type']=='blob'}
    assert len(entries)==len(bindings)==15
    assert {x['path'] for x in bindings}==set(entries)
    for x in bindings:
        assert safe(x['local'])
        p=root/x['local']; b=p.read_bytes(); e=entries[x['path']]
        assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256']
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
        assert p.stat().st_mode==x['full_mode']
        assert x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path']
    completed=json.loads((root/'private/completed-bindings.json').read_text())
    allowed=[
      'frontier/campaigns/2026-10-14/discovery-arithmetic-r162cp-parent/contribution-assessment.md',
      'frontier/campaigns/2026-10-14/arithmetic-r162cp-contribution-r1/private/REVIEW.md',
      'frontier/campaigns/2026-10-14/arithmetic-r162cp-contribution-r1/private/READING-LIMITS.md',
      'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cp/STATEMENT.md',
      'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cp/FINAL.md']
    assert [x['original'] for x in completed]==allowed
    for x in completed:
        for field,modefield in [('original','full_mode'),('copy','copy_full_mode')]:
            assert safe(x[field]); p=(project if field=='original' else root)/x[field]
            assert not p.is_symlink(); b=p.read_bytes()
            assert len(b)==x['bytes'] and sha(b)==x['sha256'] and p.stat().st_mode==x[modefield]
    for x in json.loads((root/'private/primary/bindings.json').read_text()):
        p=root/'private/primary'/(x['name']+'.pdf'); b=p.read_bytes()
        assert len(b)==x['bytes'] and sha(b)==x['sha256']
        expected=x.get('extract_sha256',x.get('text_sha256'))
        assert sha(p.with_suffix('.txt').read_bytes())==expected

def verify(root, final_sha, manifest_sha, report_sha, project=None):
    root=Path(root)
    for name,anchor in [('FINAL.md',final_sha),('MANIFEST.json',manifest_sha),('REPORT.md',report_sha)]:
        assert len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor), 'invalid anchor'
        if name in DETACHED: assert (root/name).lstat().st_mode == 33188, 'detached full-mode mismatch'
        assert sha((root/name).read_bytes())==anchor, 'detached anchor mismatch: '+name
    manifest=json.loads((root/'MANIFEST.json').read_text())
    records=check_inventory(root,manifest)
    if project is not None: check_bindings(root,project)
    return {'files':sum(x['kind']=='file' for x in records),'directories':sum(x['kind']=='dir' for x in records),'bytes':sum(x.get('bytes',0) for x in records)}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',required=True);p.add_argument('--final-sha256',required=True)
    p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True)
    p.add_argument('--project-root',required=True)
    a=p.parse_args()
    print('MATCH',json.dumps(verify(a.root,a.final_sha256,a.manifest_sha256,a.report_sha256,a.project_root),sort_keys=True))
