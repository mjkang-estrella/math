#!/usr/bin/env python3
"""Exact inventory authentication, not a mathematical proof. Original code MIT."""
import argparse,hashlib,json,os,re,stat
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
def original_base():
    # abspath normalizes dots but deliberately does not resolve symlinks.
    script=Path(os.path.abspath(__file__))
    for p in [*reversed(script.parents),script]:
        st=p.lstat()
        if stat.S_ISLNK(st.st_mode):raise ValueError('script/root/ancestor symlink forbidden')
        if p!=script and not stat.S_ISDIR(st.st_mode):raise ValueError('non-directory ancestor')
    return script.parent

def scan(base):
    files=set();dirs=set()
    def walk(p):
        for entry in os.scandir(p):
            q=Path(entry.path);rel=q.relative_to(base).as_posix();safe(rel)
            st=q.lstat()
            if stat.S_ISLNK(st.st_mode):raise ValueError('symlink forbidden: '+rel)
            if stat.S_ISDIR(st.st_mode):dirs.add(rel);walk(q)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink!=1:raise ValueError('hardlink forbidden: '+rel)
                files.add(rel)
            else:raise ValueError('nonregular object forbidden: '+rel)
    walk(base);return files,dirs

def check_rows(base,rows,actual):
    if not isinstance(rows,dict) or set(rows)!=actual:raise ValueError('file inventory mismatch')
    for name,row in rows.items():
        safe(name)
        if set(row)!={'sha256','bytes'} or type(row['bytes']) is not int or row['bytes']<0 or not re.fullmatch('[0-9a-f]{64}',row['sha256']):raise ValueError('invalid row')
        p=base/name
        if p.stat().st_size!=row['bytes'] or sha(p)!=row['sha256']:raise ValueError('payload mismatch: '+name)

def check_dirs(expected,actual):
    if not isinstance(expected,list) or len(expected)!=len(set(expected)):raise ValueError('invalid directory inventory')
    for s in expected:safe(s)
    if set(expected)!=actual:raise ValueError('directory inventory mismatch')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--verifier-sha256',required=True);ap.add_argument('--private',action='store_true');ap.add_argument('--source-tree',type=Path);a=ap.parse_args()
    base=original_base();files,dirs=scan(base)
    if sha(base/'verify.py')!=a.verifier_sha256:raise ValueError('wrong external verifier anchor')
    mp=base/'manifest.json'
    if sha(mp)!=a.manifest_sha256:raise ValueError('wrong external manifest anchor')
    m=read(mp)
    if set(m)!={'schema','status','public','private','public_dirs','private_dirs'} or m['schema']!=2 or m['status']!='COMPLETE_AUTHOR_PROOF_READY_FOR_INDEPENDENT_REVIEW':raise ValueError('manifest schema')
    public={p for p in files if not p.startswith('private/') and p!='manifest.json'}
    if any(p.endswith('/manifest.json') for p in public):raise ValueError('nested manifest')
    check_rows(base,m['public'],public)
    check_dirs(m['public_dirs'],{p for p in dirs if p!='private' and not p.startswith('private/')})
    if a.private:
        check_rows(base,m['private'],{p for p in files if p.startswith('private/')})
        check_dirs(m['private_dirs'],{p for p in dirs if p=='private' or p.startswith('private/')})
        for name in ['receipts-200.json','receipts-008.json','primary-receipts.json']:
            for r in read(base/name):
                local=r.get('local') or 'private/'+r['path'].removeprefix('preprints/')
                safe(local);p=base/local
                if sha(p)!=r['sha256'] or p.stat().st_size!=r['bytes']:raise ValueError('receipt mismatch')
                git_blob=r.get('git_blob',r.get('git_blob_sha1'))
                if git_blob is not None:
                    v=p.read_bytes();g=hashlib.sha1(b'blob '+str(len(v)).encode()+b'\0'+v).hexdigest()
                    if g!=git_blob:raise ValueError('Git blob mismatch')
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
        if len(actual)!=len(receipts) or actual!={r['path']:r.get('git_blob',r.get('git_blob_sha1')) for r in receipts}:raise ValueError('source receipts membership')
    print(json.dumps({'status':'PASS_INVENTORY_NOT_PROOF','public_files':len(m['public']),'public_directories':len(m['public_dirs']),'private_files_checked':len(m['private']) if a.private else 0,'private_directories_checked':len(m['private_dirs']) if a.private else 0,'canonical_source_tree_checked':bool(a.source_tree)}))

if __name__=='__main__':
    try:main()
    except (ValueError,OSError,KeyError,TypeError,StopIteration) as e:raise SystemExit('FAIL: '+str(e))
