# Author: Myeongjin Kang (no affiliation). SPDX-License-Identifier: MIT
"""Read-only externally anchored exact file AND directory inventory verifier."""
import argparse,hashlib,json,os,stat,sys
from pathlib import Path

def require(ok,msg):
    if not ok:raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def scan(root):
    files=[];dirs=[]
    def visit(path,rel):
        st=path.lstat()
        if stat.S_ISDIR(st.st_mode):
            dirs.append(rel)
            for child in sorted(path.iterdir(),key=lambda p:p.name):visit(child,child.relative_to(root).as_posix())
        elif stat.S_ISREG(st.st_mode):
            require(st.st_nlink==1,'hardlinked file: '+rel)
            files.append(rel)
        else:raise ValueError('link or nonregular node: '+rel)
    visit(root,'.')
    return sorted(files),sorted(dirs)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--expected-manifest-sha256',required=True);args=ap.parse_args()
    root=Path(__file__).absolute().parent
    files,dirs=scan(root)
    raw=(root/'MANIFEST.json').read_bytes()
    require(sha(raw)==args.expected_manifest_sha256,'external manifest anchor mismatch')
    m=json.loads(raw);entries=m['files'];names=[e['path'] for e in entries]
    require(len(names)==len(set(names)),'duplicate file entry')
    require(all(not Path(n).is_absolute() and '..' not in Path(n).parts and n!='MANIFEST.json' for n in names),'unsafe path')
    require(files==sorted(names+['MANIFEST.json']),'exact file inventory mismatch')
    require(dirs==m['directories'],'exact directory inventory mismatch')
    for e in entries:
        data=(root/e['path']).read_bytes();require(len(data)==e['size'] and sha(data)==e['sha256'],'payload mismatch: '+e['path'])
    tree=json.loads((root/'private/context/sources__preprints-tree.json').read_text());require(tree.get('truncated') is False,'truncated tree')
    blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
    pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    receipts=json.loads((root/'source-receipts.json').read_text())
    for e in receipts:
        data=(root/e['local']).read_bytes();git=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(git==e['git_blob']==blobs[e['path']],'source Git identity mismatch')
        require(sha(data)==e['sha256'] and len(data)==e['size'],'source receipt mismatch')
        require(e['url']=='https://raw.githubusercontent.com/openai/math/'+pin+'/'+e['path'],'unpinned source URL')
    for name,key in [('context-receipts.json','local'),('primary-receipts.json','path')]:
        for e in json.loads((root/name).read_text()):
            data=(root/e[key]).read_bytes();require(sha(data)==e['sha256'] and len(data)==e['size'],'receipt mismatch: '+name)
    print(json.dumps({'status':'PASS','files':len(entries),'directories':len(dirs),'pinned_source_bodies':len(receipts),'meaning':'exact inventory/provenance only; no mathematical or contribution PASS'}))
if __name__=='__main__':
    try:main()
    except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
