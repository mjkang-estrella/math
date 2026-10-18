#!/usr/bin/env python3
"""Read-only, caller-anchored exact payload and directory verification."""
import argparse,hashlib,json,stat,sys
from pathlib import Path

def require(ok,msg):
    if not ok: raise ValueError(msg)
def sha(b): return hashlib.sha256(b).hexdigest()
def scan(root):
    files=[];dirs=[]
    def visit(p,rel):
        s=p.lstat()
        if stat.S_ISDIR(s.st_mode):
            dirs.append(rel)
            for c in sorted(p.iterdir(),key=lambda q:q.name): visit(c,c.relative_to(root).as_posix())
        elif stat.S_ISREG(s.st_mode):
            require(s.st_nlink==1,'hardlinked file: '+rel);files.append(rel)
        else: raise ValueError('link or nonregular node: '+rel)
    visit(root,'.');return sorted(files),sorted(dirs)
def check(root,anchor):
    files,dirs=scan(root)
    raw=(root/'MANIFEST.json').read_bytes()
    require(sha(raw)==anchor,'external manifest anchor mismatch')
    m=json.loads(raw);entries=m['files'];names=[e['path'] for e in entries]
    require(len(names)==len(set(names)),'duplicate file entry')
    require(all(isinstance(n,str) and n not in ('','.', 'MANIFEST.json') and not Path(n).is_absolute() and '..' not in Path(n).parts and Path(n).as_posix()==n for n in names),'unsafe file path')
    require(files==sorted(names+['MANIFEST.json']),'exact file inventory mismatch')
    require(dirs==m['directories'],'exact directory inventory mismatch')
    for e in entries:
        b=(root/e['path']).read_bytes();require(len(b)==e['bytes'] and sha(b)==e['sha256'],'payload mismatch: '+e['path'])
    r=json.loads((root/'source-receipt.json').read_text());pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    require(r['pin']==pin,'unexpected source pin')
    selection=json.loads((root/'source-tree-selection.json').read_text())
    require(selection['pin']==pin,'unexpected selected-tree pin')
    blobs={e['path']:e['sha'] for e in selection['entries']}
    require(len(blobs)==len(r['files']),'selected-tree receipt count mismatch')
    for e in r['files']:
        require(e['local'] in names,'source body outside inventory')
        b=(root/e['local']).read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(git==e['git_blob_sha1']==blobs[e['path']],'source Git identity mismatch')
        require(sha(b)==e['sha256'] and len(b)==e['bytes'],'source receipt mismatch')
        require(e['url']=='https://raw.githubusercontent.com/openai/math/'+pin+'/'+e['path'],'unpinned source URL')
    primary=json.loads((root/'primary-receipt.json').read_text());primary_count=0
    for e in primary:
        if 'error' in e: continue
        n='private/primary/'+e['name'];b=(root/(n+'.pdf')).read_bytes();t=(root/(n+'.txt')).read_bytes()
        require(len(b)==e['bytes'] and sha(b)==e['sha256'] and sha(t)==e['text_sha256'],'primary receipt mismatch: '+e['name']);primary_count+=1
    h=json.loads((root/'history-index.json').read_text())
    require(selection['complete_tree_sha256']==h['source_inputs']['sources/preprints-tree.json'],'tree provenance mismatch')
    replay=json.loads((root/'history-replay-result.json').read_text())
    require(replay['byte_identical'] is True and replay['sha256']==sha((root/'history-index.json').read_bytes()),'index replay identity mismatch')
    artifacts={x['path']:x for x in h['artifacts']}
    for v in json.loads((root/'history-adjudications.json').read_text()).values():
        for e in v.get('evidence',[]):require(e['path'] in artifacts and artifacts[e['path']]['sha256']==e['sha256'],'adjudication input identity mismatch')
    collaboration=json.loads((root/'author-collaboration.json').read_text())
    require(sha((root/'assembly-proof.md').read_bytes())==collaboration['assembly']['sha256'],'copied assembly identity mismatch')
    require(sha((root/'paid-profile-bridge.md').read_bytes())==collaboration['antecedent']['sha256'],'copied antecedent identity mismatch')
    return {'status':'PASS','payload_files':len(entries),'directories':len(dirs),'pinned_blobs':len(r['files']),'primary_bodies':primary_count,'scope':'exact inventory and recorded identities; not mathematical proof, novelty, or independent review'}
def main():
    p=argparse.ArgumentParser();p.add_argument('--expected-manifest-sha256',required=True);p.add_argument('--root',type=Path);a=p.parse_args()
    root=a.root.absolute() if a.root else Path(__file__).absolute().parent
    print(json.dumps(check(root,a.expected_manifest_sha256)))
if __name__=='__main__':
    try: main()
    except Exception as e: print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
