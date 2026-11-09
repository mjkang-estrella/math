#!/usr/bin/env python3
"""Read-only packet authentication. Explicit detached anchors are mandatory.
This is not a mathematical proof/contribution verifier. Run with python -B.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

REL = 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ch'
PROJECT = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PREFIX = 'preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026'
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
COMPLETED = {
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162cg-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cg/private/DERIVATION.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cg/private/WORKING.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cg/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cg/FINAL.md',
}
PRIMARY = {'SW16','DM21','Hikita','HHKKO','BEPS','MR','AN'}
ENVELOPES = {'MANIFEST.json','REPORT.md'}
REGULAR = stat.S_IFREG | 0o644


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe(s, directory=False):
    assert isinstance(s,str) and s and '\\' not in s and '\x00' not in s
    if s=='.':
        assert directory
        return
    p=PurePosixPath(s)
    assert not p.is_absolute() and str(p)==s and all(x not in ('','.','..') for x in p.parts), 'unsafe path'


def snapshot(root):
    assert stat.S_ISDIR(root.lstat().st_mode) and not root.is_symlink()
    files={}; dirs={'.':root.lstat().st_mode}
    def walk(p):
        for ent in sorted(os.scandir(p),key=lambda e:e.name):
            q=Path(ent.path); rel=q.relative_to(root).as_posix(); mode=q.lstat().st_mode
            safe(rel)
            if stat.S_ISDIR(mode):
                dirs[rel]=mode; walk(q)
            else:
                assert stat.S_ISREG(mode), 'nonregular member: '+rel
                files[rel]=(q.read_bytes(),mode)
    walk(root)
    return files,dirs


def make_manifest(root):
    files,dirs=snapshot(root)
    assert not (ENVELOPES & set(files)), 'seal files already exist'
    return {'schema':1,'root':REL,
      'files':[{'path':k,'bytes':len(v[0]),'sha256':sha(v[0]),'full_mode':v[1]} for k,v in sorted(files.items())],
      'directories':[{'path':k,'full_mode':v} for k,v in sorted(dirs.items())]}


def serialize(obj):
    return (json.dumps(obj,indent=2,sort_keys=True)+'\n').encode()


def report_bytes(m, final_anchor, manifest_anchor):
    return (f"""# r162ch detached artifact report

Mathematical disposition: PREFREEZE / no nominee. No mathematical gate or count.

FINAL SHA256: {final_anchor}
MANIFEST SHA256: {manifest_anchor}
Payload files: {len(m['files'])}
Whole-root files including MANIFEST and REPORT: {len(m['files'])+2}
Directories including root: {len(m['directories'])}

Sorted unique records and exact safe membership, bytes, SHA256, full st_mode,
source Git blobs/trees and pinned complete-tree bindings, primary bindings, and
five exact completed originals/copies are checked by the read-only verifier.
Initial completed receipts captured permission bits only; full modes were bound late.

Before writing this one seal, the SAME final core and binding logic passed with
in-memory MANIFEST/REPORT bytes. Tiny copied controls exercise artifact logic only.
REPORT is outside the manifest payload list and inside the exclusive write root.
Its SHA256 is detached in the final response. No sealed file is changed afterward.

Run verify.py with all three explicit --final-sha256, --manifest-sha256 and
--report-sha256 anchors. A successful run authenticates artifacts, not mathematics.
""").encode()


def verify_core(root, anchors, virtual=None):
    virtual=virtual or {}
    assert set(virtual)<=ENVELOPES
    files,dirs=snapshot(root)
    assert not (set(virtual)&set(files)), 'virtual files must not replace actual files'
    files.update(virtual)
    for name,key in [('FINAL.md','final'),('MANIFEST.json','manifest'),('REPORT.md','report')]:
        assert re.fullmatch('[0-9a-f]{64}',anchors[key]), 'invalid explicit anchor'
        assert name in files and sha(files[name][0])==anchors[key], 'detached anchor mismatch: '+name
    for name in ENVELOPES:
        assert files[name][1]==REGULAR, 'envelope full mode mismatch'
    m=json.loads(files['MANIFEST.json'][0])
    assert m['schema']==1 and m['root']==REL
    for kind in ['files','directories']:
        names=[x['path'] for x in m[kind]]
        assert names==sorted(names) and len(names)==len(set(names)), 'unsorted/duplicate records'
        for name in names: safe(name,kind=='directories')
    recorded={x['path']:x for x in m['files']}
    assert not (set(recorded)&ENVELOPES)
    assert set(files)==set(recorded)|ENVELOPES, 'file membership mismatch'
    assert dirs=={x['path']:x['full_mode'] for x in m['directories']}, 'directory membership/mode mismatch'
    for name,rec in recorded.items():
        data,mode=files[name]
        assert mode==rec['full_mode'], 'file full mode mismatch: '+name
        assert len(data)==rec['bytes'] and sha(data)==rec['sha256'], 'payload mismatch: '+name
    assert files['REPORT.md'][0]==report_bytes(m,anchors['final'],anchors['manifest']), 'report content mismatch'
    return m


def verify_bindings(root):
    def readj(name): return json.loads((root/name).read_bytes())
    raw=(PROJECT/'sources/preprints-tree.json').read_bytes()
    assert len(raw)==4858136 and sha(raw)==TREE_SHA
    whole=json.loads(raw); entries=whole['tree'] if isinstance(whole,dict) else whole
    assert len(entries)==13223
    selected=[x for x in entries if x['path']==PREFIX or x['path'].startswith(PREFIX+'/')]
    local=readj('private/tree-selection.json')
    assert local==selected and len(local)==14
    bypath={x['path']:x for x in local}
    assert len(bypath)==14
    bindings=readj('private/source-bindings.json')
    assert len(bindings)==11 and len({x['path'] for x in bindings})==11
    assert {x['upstream'] for x in bindings}=={x['path'] for x in local if x['type']=='blob'}
    for rec in bindings:
        up=rec['upstream']; ent=bypath[up]
        expected='private/source/'+up[len(PREFIX)+1:]
        assert rec['path']==expected
        assert rec['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+up
        data=(root/expected).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert blob==ent['sha']==rec['blob']
        assert len(data)==ent['size']==rec['bytes'] and sha(data)==rec['sha256']
        assert oct(stat.S_IMODE((root/expected).lstat().st_mode))==rec['mode']
    trees=[x for x in local if x['type']=='tree']
    assert len(trees)==3
    for ent in trees:
        parent=ent['path']
        children=[x for x in local if str(PurePosixPath(x['path']).parent)==parent]
        children.sort(key=lambda x:(PurePosixPath(x['path']).name+('/' if x['type']=='tree' else '')).encode())
        body=b''
        for child in children:
            mode='40000' if child['type']=='tree' else child['mode']
            body+=mode.encode()+b' '+PurePosixPath(child['path']).name.encode()+b'\0'+bytes.fromhex(child['sha'])
        assert hashlib.sha1(b'tree '+str(len(body)).encode()+b'\0'+body).hexdigest()==ent['sha']
    receipts=readj('private/completed-bindings.json')
    full=readj('private/completed-full-modes.json')
    assert len(receipts)==len(full)==5
    assert {x['original'] for x in receipts}==COMPLETED=={x['original'] for x in full}
    late={x['original']:x for x in full}
    for rec in receipts:
        safe(rec['copy']); assert rec['copy'].startswith('private/completed/')
        orig=PROJECT/rec['original']; cp=root/rec['copy']; later=late[rec['original']]
        om=orig.lstat().st_mode; cm=cp.lstat().st_mode
        assert stat.S_ISREG(om) and stat.S_ISREG(cm)
        assert oct(stat.S_IMODE(om))==rec['original_mode'] and oct(stat.S_IMODE(cm))==rec['copy_mode']
        assert om==later['original_full_mode'] and cm==later['copy_full_mode']
        a=orig.read_bytes(); b=cp.read_bytes()
        assert a==b and len(a)==rec['bytes']==later['bytes'] and sha(a)==rec['sha256']==later['sha256']
        assert later['copy']==rec['copy']
    prim=readj('private/primary/bindings.json'); ledger=readj('private/primary/read-ledger.json')
    assert len(prim)==len(ledger)==7 and {x['id'] for x in prim}==PRIMARY=={x['id'] for x in ledger}
    texts={x['id']:x for x in ledger}
    for rec in prim:
        name=rec['id']; data=(root/'private/primary'/(name+'.pdf')).read_bytes()
        txt=(root/'private/primary'/(name+'.txt')).read_bytes()
        assert len(data)==rec['bytes'] and sha(data)==rec['sha256']
        assert len(txt)==rec['text_bytes'] and sha(txt)==texts[name]['txt_sha256']
    return {'source_blobs':11,'source_trees':3,'primary_PDFs':7,'completed_pairs':5}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--final-sha256',required=True); ap.add_argument('--manifest-sha256',required=True); ap.add_argument('--report-sha256',required=True)
    a=ap.parse_args()
    assert Path.cwd()==PROJECT, 'use the authorized command workdir'
    root=PROJECT/REL
    anchors={'final':a.final_sha256,'manifest':a.manifest_sha256,'report':a.report_sha256}
    m=verify_core(root,anchors); bindings=verify_bindings(root)
    print(json.dumps({'artifact_result':'MATCH','payload_files':len(m['files']),'whole_root_files':len(m['files'])+2,'directories_including_root':len(m['directories']),**bindings,'mathematical_gate':None},sort_keys=True))

if __name__=='__main__': main()
