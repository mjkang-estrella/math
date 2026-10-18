#!/usr/bin/env python3
"""Read-only exact-inventory authentication. Identity only. SPDX-License-Identifier: MIT."""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def fail(s): raise ValueError(s)
def ancestry(p):
    # Inspect the original absolute spelling BEFORE any resolution.
    for q in reversed([p, *p.parents]):
        st=os.lstat(q)
        if stat.S_ISLNK(st.st_mode): fail('symlink ancestry: '+str(q))
        if not stat.S_ISDIR(st.st_mode): fail('non-directory ancestry: '+str(q))
def scan(root):
    files={};dirs=[]
    def walk(p):
        for e in sorted(os.scandir(p),key=lambda x:x.name):
            q=Path(e.path);r=q.relative_to(root).as_posix();s=os.lstat(q)
            if stat.S_ISLNK(s.st_mode): fail('symlink payload: '+r)
            if stat.S_ISDIR(s.st_mode): dirs.append(r);walk(q)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink!=1: fail('hardlink: '+r)
                if q.name=='manifest.json' and r!='manifest.json': fail('nested manifest: '+r)
                files[r]={'bytes':s.st_size,'sha256':sha(q)}
            else: fail('nonregular entry: '+r)
    walk(root);return files,sorted(dirs)
def verify(root,anchor):
    ancestry(root)
    m=root/'manifest.json';s=os.lstat(m)
    if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1: fail('manifest nonregular or hardlink')
    if sha(m)!=anchor: fail('external manifest anchor mismatch')
    data=json.loads(m.read_text())
    files,dirs=scan(root);files.pop('manifest.json')
    if files!=data['files'] or dirs!=data['directories']: fail('exact inventory mismatch')
    src=json.loads((root/'source-identities.json').read_text())
    if src['pin']!='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb':fail('source pin')
    if src['complete_tree_sha256']!='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' or src['complete_tree_entries']!=13223 or src['truncated'] is not False:fail('complete tree identity')
    expected=set()
    for e in src['source_blobs']:
        r='private/'+e['path'];expected.add(r);b=(root/r).read_bytes()
        if len(b)!=e['size'] or hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()!=e['sha']:fail('canonical source mismatch: '+r)
    if len(expected)!=21 or expected!={r for r in files if r.startswith('private/preprints/')}:fail('source completeness mismatch')
    primary=json.loads((root/'primary-receipts.json').read_text())
    if {e['path'] for e in primary}!={r for r in files if r.startswith('private/primary/')} or len(primary)!=10:fail('primary completeness mismatch')
    for e in primary:
        if files[e['path']]!={k:e[k] for k in ('bytes','sha256')}:fail('primary receipt mismatch')
    for e in json.loads((root/'provenance/copy-receipts.json').read_text()):
        if sha(root/e['copy'])!=e['sha256']:fail('provenance copy mismatch')
    build=json.loads((root/'development/build05/build-receipt.json').read_text())
    if build['layout_or_reference_warnings']:fail('build warnings')
    for name,h in build['source_files'].items():
        if sha(root/'public'/name)!=h:fail('build source mismatch')
    pdf=sha(root/'output/pdf/article.pdf')
    if pdf!=build['pdf_sha256'] or pdf!=sha(root/'development/copied-build-final/article.pdf'):fail('PDF rebuild mismatch')
    inspection=json.loads((root/'inspection/page-inspection.json').read_text())
    if inspection['pdf_sha256']!=pdf or inspection['pages']!=13 or len(inspection['page_records'])!=13:fail('inspection scope mismatch')
    for e in inspection['page_records']:
        if sha(root/e['path'])!=e['sha256'] or not e['visually_checked']:fail('page inspection mismatch')
    public=json.loads((root/'public-source-inventory.json').read_text())
    actual={r.removeprefix('public/'):v for r,v in files.items() if r.startswith('public/')}
    if actual!=public['files']:fail('public source inventory mismatch')
    for r,v in actual.items():
        p=root/'development/copied-source'/r
        if p.stat().st_size!=v['bytes'] or sha(p)!=v['sha256']:fail('copied public source mismatch')
    for e in json.loads((root/'input-anchors.json').read_text()):
        if sha(root/e['copy'])!=e['sha256']:fail('frozen input anchor mismatch')
    cert=sha(root/'public/code/finite-proof-certificate.json')
    finite=json.loads((root/'development/finite-replay.stdout').read_text())
    if finite['status']!='PASS_FINITE_BASES' or finite['certificate_sha256']!=cert:fail('finite replay identity mismatch')
    return {'result':'PASS_MANUSCRIPT_IDENTITY_ONLY','payload_files':len(files),'total_files':len(files)+1,'directories':len(dirs),'canonical_source_blobs':21,'primary_files':10,'pages':13,'pdf_sha256':pdf}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);a=p.parse_args()
    try:
        root=Path(os.path.abspath(__file__)).parent
        print(json.dumps(verify(root,a.anchor),sort_keys=True))
    except Exception as e:
        print('INTEGRITY_REJECT: '+str(e),file=sys.stderr);sys.exit(1)
