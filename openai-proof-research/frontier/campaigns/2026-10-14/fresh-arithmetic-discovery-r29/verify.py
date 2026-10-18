#!/usr/bin/env python3
"""External-anchor exact-inventory verifier. MIT. Never writes or reseals."""
import argparse,hashlib,json,os,stat,sys
from pathlib import Path

def die(s): raise ValueError(s)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ancestry(p):
    p=Path(os.path.abspath(p))
    for q in [p,*p.parents]:
        st=q.lstat()
        if stat.S_ISLNK(st.st_mode):die('symlink ancestry: '+str(q))
    return p

def scan(root):
    files={};dirs=[]
    def visit(d):
        for ent in sorted(os.scandir(d),key=lambda e:e.name):
            p=Path(ent.path);s=p.lstat();rel=p.relative_to(root).as_posix()
            if stat.S_ISLNK(s.st_mode):die('symlink: '+rel)
            if stat.S_ISDIR(s.st_mode):dirs.append(rel);visit(p)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink!=1:die('hardlink: '+rel)
                if p.name=='manifest.json' and rel!='manifest.json':die('nested manifest')
                files[rel]={'sha256':digest(p),'bytes':s.st_size}
            else:die('nonregular: '+rel)
    visit(root);return files,dirs

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root');ap.add_argument('--expected-manifest',required=True);ap.add_argument('--expected-verifier',required=True);ap.add_argument('--public-only',action='store_true');ap.add_argument('--source-tree');a=ap.parse_args()
    script=ancestry(__file__);root=ancestry(a.root or script.parent)
    if digest(script)!=a.expected_verifier:die('executing verifier external anchor mismatch')
    if not root.is_dir():die('root is not a directory')
    files,dirs=scan(root)
    if files.get('verify.py',{}).get('sha256')!=a.expected_verifier:die('packet verifier external anchor mismatch')
    if files.get('manifest.json',{}).get('sha256')!=a.expected_manifest:die('manifest external anchor mismatch')
    m=json.loads((root/'manifest.json').read_text())
    expected=dict(m['files']);expected_dirs=list(m['directories'])
    if not a.public_only:expected.update(m['private_files']);expected_dirs+=m['private_directories']
    actual={k:v for k,v in files.items() if k!='manifest.json'}
    if actual!=expected:die('exact file inventory/hash mismatch')
    if sorted(dirs)!=sorted(expected_dirs):die('exact directory inventory mismatch')
    blobs=0
    if a.source_tree:
        if a.public_only:die('source body verification requires private files')
        tree=json.loads(Path(a.source_tree).read_text())
        if tree.get('truncated') is not False:die('source tree incomplete')
        entries={x['path']:x for x in tree['tree'] if x['type']=='blob'}
        receipts=[]
        for name in ['source047-receipts.json','companion-receipts.json']:receipts+=json.loads((root/name).read_text())
        fams={x['path'].split('/')[1] for x in receipts}
        all_paths={p for p in entries if p.split('/')[1] in fams and not p.endswith('.pdf')}
        if {x['path'] for x in receipts}!=all_paths or len(receipts)!=len(all_paths):die('source family completeness')
        for x in receipts:
            b=(root/x['local']).read_bytes();g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            if g!=entries[x['path']]['sha'] or g!=x['git_blob_sha1'] or hashlib.sha256(b).hexdigest()!=x['sha256']:die('source identity')
        blobs=len(receipts)
    print(json.dumps({'status':'PASS','public_payloads':len(m['files']),'private_payloads':0 if a.public_only else len(m['private_files']),'authenticated_source_blobs':blobs},sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
