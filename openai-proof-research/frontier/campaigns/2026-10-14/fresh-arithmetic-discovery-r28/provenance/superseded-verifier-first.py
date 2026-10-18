#!/usr/bin/env python3
"""Exact inventory authentication, not a mathematical proof. Original code MIT."""
import argparse,hashlib,json,re
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pairs(xs):
    d={}
    for k,v in xs:
        if k in d:raise ValueError('duplicate JSON key')
        d[k]=v
    return d

def read(p):return json.loads(p.read_text(),object_pairs_hook=pairs)
def safe(s):
    if not isinstance(s,str) or not s or s.startswith('/') or '\\' in s or any(x in ('','.','..') for x in s.split('/')):raise ValueError('unsafe path')
def check_rows(base,rows,actual):
    if not isinstance(rows,dict) or set(rows)!=actual:raise ValueError('inventory mismatch')
    for name,row in rows.items():
        safe(name)
        if set(row)!={'sha256','bytes'} or type(row['bytes']) is not int or row['bytes']<0 or not re.fullmatch('[0-9a-f]{64}',row['sha256']):raise ValueError('invalid row')
        p=base/name
        if p.is_symlink() or not p.is_file() or p.stat().st_size!=row['bytes'] or sha(p)!=row['sha256']:raise ValueError('payload mismatch: '+name)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--verifier-sha256',required=True);ap.add_argument('--private',action='store_true');ap.add_argument('--source-tree',type=Path);a=ap.parse_args()
    base=Path(__file__).resolve().parent
    if sha(base/'verify.py')!=a.verifier_sha256:raise ValueError('wrong external verifier anchor')
    mp=base/'manifest.json'
    if sha(mp)!=a.manifest_sha256:raise ValueError('wrong external manifest anchor')
    m=read(mp)
    if set(m)!={'schema','status','public','private'} or m['schema']!=1 or m['status']!='COMPLETE_AUTHOR_PROOF_READY_FOR_INDEPENDENT_REVIEW':raise ValueError('manifest schema')
    allpaths=list(base.rglob('*'))
    if any(p.is_symlink() for p in allpaths):raise ValueError('symlink forbidden')
    public={p.relative_to(base).as_posix() for p in allpaths if p.is_file() and p.relative_to(base).parts[0]!='private' and p.name!='manifest.json'}
    # Only the root manifest is exempt from public membership.
    if any(p.name=='manifest.json' and p!=mp and p.relative_to(base).parts[0]!='private' for p in allpaths):raise ValueError('nested manifest')
    check_rows(base,m['public'],public)
    if a.private:
        private={p.relative_to(base).as_posix() for p in allpaths if p.is_file() and p.relative_to(base).parts[0]=='private'}
        check_rows(base,m['private'],private)
        for name in ['receipts-200.json','receipts-008.json','primary-receipts.json']:
            for r in read(base/name):
                p=base/r['local'];safe(r['local'])
                if sha(p)!=r['sha256'] or p.stat().st_size!=r['bytes']:raise ValueError('receipt mismatch')
                if 'git_blob' in r:
                    v=p.read_bytes();g=hashlib.sha1(b'blob '+str(len(v)).encode()+b'\0'+v).hexdigest()
                    if g!=r['git_blob']:raise ValueError('Git blob mismatch')
    if a.source_tree:
        expected=next(r['sha256'] for r in read(base/'context-receipts.json') if r['path']=='sources/preprints-tree.json')
        if sha(a.source_tree)!=expected:raise ValueError('canonical tree identity')
        t=read(a.source_tree)
        if t['truncated'] is not False:raise ValueError('truncated source tree')
        inv=read(base/'source-family-inventory.json')
        rows=[r for r in t['tree'] if r['type']=='blob' and any(r['path'].startswith(p) for p in inv['family_prefixes'])]
        if rows!=inv['canonical_blobs']:raise ValueError('source family membership')
        actual={r['path']:r['sha'] for r in rows if not r['path'].lower().endswith('.pdf')}
        receipts=read(base/'receipts-200.json')+read(base/'receipts-008.json')
        if actual!={r['path']:r['git_blob'] for r in receipts}:raise ValueError('source receipts membership')
    print(json.dumps({'status':'PASS_INVENTORY_NOT_PROOF','public_files':len(m['public']),'private_files_checked':len(m['private']) if a.private else 0,'canonical_source_tree_checked':bool(a.source_tree)}))

if __name__=='__main__':
    try:main()
    except (ValueError,OSError,KeyError,TypeError,StopIteration) as e:raise SystemExit('FAIL: '+str(e))
