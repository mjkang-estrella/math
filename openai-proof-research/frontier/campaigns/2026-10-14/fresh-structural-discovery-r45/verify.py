#!/usr/bin/env python3
"""MIT. Read-only verification against a REQUIRED caller-supplied anchor."""
import argparse, hashlib, json, stat, sys
from pathlib import Path
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
def require(ok,why):
    if not ok:raise ValueError(why)
def safe(n):
    return isinstance(n,str) and n not in ('','.') and not Path(n).is_absolute() and '..' not in Path(n).parts and Path(n).as_posix()==n

def scan(root):
    files=[];dirs=[]
    def walk(p,rel):
        s=p.lstat()
        if stat.S_ISDIR(s.st_mode):
            dirs.append(rel)
            for q in sorted(p.iterdir(),key=lambda x:x.name):walk(q,q.relative_to(root).as_posix())
        elif stat.S_ISREG(s.st_mode):
            require(s.st_nlink==1,'hardlinked regular file: '+rel)
            require(p.name!='MANIFEST.json' or rel=='MANIFEST.json','nested manifest: '+rel)
            files.append(rel)
        else:raise ValueError('symlink or nonregular node: '+rel)
    walk(root,'.')
    return sorted(files),sorted(dirs)

def check(root,anchor):
    files,dirs=scan(root)
    raw=(root/'MANIFEST.json').read_bytes()
    require(sha(raw)==anchor,'external manifest anchor mismatch')
    m=json.loads(raw);entries=m['files'];names=[e['path'] for e in entries]
    require(len(names)==len(set(names)) and all(safe(n) and n!='MANIFEST.json' for n in names),'invalid payload names')
    require(files==sorted(names+['MANIFEST.json']),'exact file inventory mismatch')
    require(dirs==m['directories'],'exact directory inventory mismatch')
    for e in entries:
        b=(root/e['path']).read_bytes()
        require(len(b)==e['bytes'] and sha(b)==e['sha256'],'payload mismatch: '+e['path'])
    require(sha((root/'scope-status.txt').read_bytes())=='7c203c60a7f7472de3f46c81d5e253822ae6a515a34404e494e4f0bead7df425','scope status changed')
    r=json.loads((root/'source-receipts.json').read_text());s=json.loads((root/'source-tree-selection.json').read_text())
    require(r['pin']==s['pin']==PIN and s['complete_tree_truncated'] is False,'source pin or tree provenance mismatch')
    blobs={e['path']:e['sha'] for e in s['entries']}
    require(len(blobs)==len(s['entries'])==len(r['files'])==14,'source selection count mismatch')
    require(set(blobs)=={e['path'] for e in r['files']},'source path selection mismatch')
    for e in r['files']:
        require(e['local'] in names,'source body outside inventory')
        b=(root/e['local']).read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(git==e['git_blob_sha1']==blobs[e['path']],'Git identity mismatch: '+e['path'])
        require(sha(b)==e['sha256'] and len(b)==e['bytes'],'source receipt mismatch')
        require(e['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path'],'unpinned source URL')
    p=json.loads((root/'primary-receipts.json').read_text())
    require(len(p)==2 and len({e['key'] for e in p})==2,'primary selection count mismatch')
    for e in p:
        require(safe(e['pdf']) and safe(e['text']) and e['pdf'] in names and e['text'] in names,'unsafe or unlisted primary path')
        b=(root/e['pdf']).read_bytes();t=(root/e['text']).read_bytes()
        require(sha(b)==e['pdf_sha256'] and sha(t)==e['text_sha256'],'primary identity mismatch')
    return {'status':'PASS','payload_files':len(entries),'directories':len(dirs),'pinned_blobs':len(r['files']),'primary_pdf_text_pairs':len(p),'scope':'Exact inventory and recorded identities only; not proof, novelty, formal verification, or independent review.'}
def main():
    p=argparse.ArgumentParser();p.add_argument('--expected-manifest-sha256',required=True);p.add_argument('--root',type=Path);a=p.parse_args()
    root=a.root.absolute() if a.root else Path(__file__).absolute().parent
    print(json.dumps(check(root,a.expected_manifest_sha256)))
if __name__=='__main__':
    try:main()
    except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
