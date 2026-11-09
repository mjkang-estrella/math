#!/usr/bin/env python3
"""Read-only explicit-anchor verification. Artifact checks, never math gates."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

EXCLUDED = {'MANIFEST.json', 'REPORT.md'}
ORIGINALS = [
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162be-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162be/private/DERIVATIONS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162be/private/WORKING.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162be/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162be/FINAL.md',
]
PREFIXES = [
 'preprints/A-Low-Space-Algorithm-for-Worst-Case-Subset-Sum-September-26-2026',
 'preprints/Subset-Sum-in-Time-2-power-0-49n-October-4-2026',
]

def sha(data): return hashlib.sha256(data).hexdigest()

def safe(name, directory=False):
    assert isinstance(name,str) and name and '\\' not in name and '\x00' not in name
    if directory and name == '.': return
    p=PurePosixPath(name)
    assert not p.is_absolute() and all(x not in ('..','.') for x in p.parts)
    assert p.as_posix()==name

def inventory(root):
    assert stat.S_ISDIR(root.lstat().st_mode)
    files={}; directories={'.':root.lstat().st_mode}
    stack=[root]
    while stack:
        d=stack.pop()
        for e in os.scandir(d):
            p=Path(e.path); name=p.relative_to(root).as_posix(); s=e.stat(follow_symlinks=False)
            safe(name)
            if stat.S_ISDIR(s.st_mode): directories[name]=s.st_mode; stack.append(p)
            else:
                assert stat.S_ISREG(s.st_mode), ('nonregular member',name)
                files[name]=(s.st_size,s.st_mode)
    return files,directories

def verify_envelope(root, final_sha, manifest_sha, report_sha):
    for name,anchor in [('FINAL.md',final_sha),('MANIFEST.json',manifest_sha),('REPORT.md',report_sha)]:
        assert len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor)
        assert stat.S_ISREG((root/name).lstat().st_mode)
        assert sha((root/name).read_bytes())==anchor, ('anchor mismatch',name)
    manifest=json.loads((root/'MANIFEST.json').read_bytes())
    assert manifest['schema']=='r162bf-seal-v1'
    rows=manifest['files']; names=[x['path'] for x in rows]
    assert names==sorted(names) and len(names)==len(set(names))
    assert not (set(names)&EXCLUDED) and 'FINAL.md' in names
    for name in names: safe(name)
    dirs=manifest['directories']; dnames=[x['path'] for x in dirs]
    assert dnames==sorted(dnames) and len(dnames)==len(set(dnames))
    for name in dnames: safe(name,True)
    files,actualdirs=inventory(root)
    assert set(files)==set(names)|EXCLUDED, 'exact file membership mismatch'
    assert actualdirs=={x['path']:x['mode'] for x in dirs}, 'directory membership/mode mismatch'
    for name in EXCLUDED: assert files[name][1]==stat.S_IFREG|0o644
    for row in rows:
        assert files[row['path']]==(row['bytes'],row['mode']), ('length/mode mismatch',row['path'])
        assert sha((root/row['path']).read_bytes())==row['sha256'], ('payload hash mismatch',row['path'])
    assert next(x for x in rows if x['path']=='FINAL.md')['sha256']==final_sha
    return len(rows),sum(x['bytes'] for x in rows),len(files),len(dirs)

def verify_bindings(root,project):
    copies=json.loads((root/'private/context/copies.json').read_bytes())
    assert [x['original'] for x in copies]==ORIGINALS
    for i,row in enumerate(copies,1):
        assert row['copy']==f'private/context/completed-{i}.md'
        original=project/row['original']; copied=root/row['copy']
        assert original.lstat().st_mode==int(row['mode'],8)
        assert stat.S_ISREG(original.lstat().st_mode)
        data=original.read_bytes()
        assert len(data)==row['bytes'] and sha(data)==row['sha256']
        assert copied.read_bytes()==data
    tree=json.loads((root/'private/source/selected-tree.json').read_bytes())
    assert len(tree)==29 and len({x['path'] for x in tree})==29
    for x in tree:
        safe(x['path'])
        assert any(x['path']==p or x['path'].startswith(p+'/') for p in PREFIXES)
    blobs={x['path']:x for x in tree if x['type']=='blob'}
    auth=json.loads((root/'private/source/authentication.json').read_bytes())
    assert len(blobs)==len(auth)==24 and {x['path'] for x in auth}==set(blobs)
    texts=[]
    for row in auth:
        p=root/'private/source'/row['path']; data=p.read_bytes(); t=blobs[row['path']]
        assert len(data)==row['bytes']==t['size'] and sha(data)==row['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob']==t['sha']
        assert row['mode']==t['mode'] and p.lstat().st_mode==int(t['mode'],8)
        assert row['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+row['path']
        if not row['path'].endswith('.pdf'): texts.append(data)
    assert len(texts)==22 and sum(map(len,texts))==244917
    access=json.loads((root/'private/primary/access.json').read_bytes())
    assert len(access)==8 and {x['name'] for x in access}=={'NW','BCKM','AKKM','AKKN','CJRS','RW','LSF','KLM'}
    for row in access:
        data=(root/'private/primary'/(row['name']+'.pdf')).read_bytes()
        assert len(data)==row['bytes'] and sha(data)==row['sha256']

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--report-sha256',required=True)
    args=ap.parse_args()
    root=Path(__file__).absolute().parent
    # Fixed mandated project; no ancestor inventory or task discovery.
    project=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
    counts=verify_envelope(root,args.final_sha256,args.manifest_sha256,args.report_sha256)
    verify_bindings(root,project)
    print(json.dumps({'artifact_verification':'MATCH','payload_records':counts[0],
      'payload_bytes':counts[1],'whole_root_files':counts[2],'directories_including_root':counts[3],
      'completed_originals_and_copies':5,'source_blobs':24,'primary_pdfs':8,
      'mathematical_gate':False}))
