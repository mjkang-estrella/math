#!/usr/bin/env python3
"""Read-only byte verifier. Explicit out-of-band anchors are mandatory.
No mathematical, historical isolation, OS-wide, or whole-parent certificate.
"""
import argparse, hashlib, json, os
from pathlib import Path, PurePosixPath
ENVELOPES={'MANIFEST.json','FINAL.md','REPORT.md','DETACHED-SHA256.json'}
TREE_SHA='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
def sha(b):return hashlib.sha256(b).hexdigest()
def verify(root,anchors):
    root=Path(root)
    if root.is_symlink():raise ValueError('root symlink')
    actual={}
    for cur,dirs,files in os.walk(root,followlinks=False):
        for name in dirs+files:
            p=Path(cur)/name
            if p.is_symlink():raise ValueError('symlink: '+str(p.relative_to(root)))
        for name in files:
            p=Path(cur)/name
            if not p.is_file():raise ValueError('nonregular file')
            actual[p.relative_to(root).as_posix()]=p
    if not ENVELOPES<=actual.keys():raise ValueError('missing envelope')
    for name,h in anchors.items():
        if len(h)!=64 or sha(actual[name].read_bytes())!=h:raise ValueError('anchor mismatch: '+name)
    detached=json.loads(actual['DETACHED-SHA256.json'].read_bytes())
    if detached!=anchors:raise ValueError('detached anchor disagreement')
    m=json.loads(actual['MANIFEST.json'].read_bytes())
    if m.get('schema')!='r137-artifact-v1' or set(m.get('excluded_envelopes',[]))!=ENVELOPES:raise ValueError('schema')
    expected={}
    for x in m['files']:
        name=x['path'];p=PurePosixPath(name)
        if p.is_absolute() or '..' in p.parts or p.as_posix()!=name or name in ENVELOPES or name in expected:raise ValueError('unsafe/duplicate manifest path')
        expected[name]=x
    if set(actual)-ENVELOPES!=set(expected):raise ValueError('exact payload membership mismatch')
    for name,x in expected.items():
        b=actual[name].read_bytes()
        if len(b)!=x['size'] or sha(b)!=x['sha256']:raise ValueError('payload mismatch: '+name)
    def local(name):
        if name not in expected:raise ValueError('unmanifested ledger target: '+name)
        return actual[name].read_bytes()
    checked={'payload_files':len(expected),'source_files':0,'primary_versions':0,'original_snapshots':0}
    if 'source-ledger.json' in expected:
        raw=local('private/preprints-tree.json');t=json.loads(raw)
        if sha(raw)!=TREE_SHA or len(t['tree'])!=13223:raise ValueError('tree identity')
        tree={x['path']:x for x in t['tree'] if x['type']=='blob'}
        for x in json.loads(local('source-ledger.json')):
            b=local(x['local']);v=tree[x['path']]
            blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            if len(b)!=x['size'] or len(b)!=v['size'] or blob!=x['gitblob'] or blob!=v['sha'] or sha(b)!=x['sha256']:raise ValueError('source identity')
            checked['source_files']+=1
    if 'primary-ledger.json' in expected:
        for x in json.loads(local('primary-ledger.json')):
            b=local(x['raw_local'])
            if len(b)!=x['size'] or sha(b)!=x['sha256']:raise ValueError('primary raw identity')
            for y in x['members']:
                b=local(y['path'])
                if len(b)!=y['size'] or sha(b)!=y['sha256']:raise ValueError('primary extract identity')
            checked['primary_versions']+=1
    if 'original-ledger.json' in expected:
        for x in json.loads(local('original-ledger.json')):
            if 'local' not in x:continue
            b=local(x['local'])
            if len(b)!=x['size'] or sha(b)!=x['sha256']:raise ValueError('original snapshot identity')
            checked['original_snapshots']+=1
    return checked
if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('--root',required=True)
    a.add_argument('--manifest-sha256',required=True)
    a.add_argument('--final-sha256',required=True)
    a.add_argument('--report-sha256',required=True)
    p=a.parse_args()
    try:
        print(json.dumps({'artifact_verification':'matched','scope':'bytes only',**verify(p.root,{'MANIFEST.json':p.manifest_sha256,'FINAL.md':p.final_sha256,'REPORT.md':p.report_sha256})},sort_keys=True))
    except Exception as e:
        print(json.dumps({'artifact_verification':'rejected','reason':str(e)}));raise SystemExit(1)
