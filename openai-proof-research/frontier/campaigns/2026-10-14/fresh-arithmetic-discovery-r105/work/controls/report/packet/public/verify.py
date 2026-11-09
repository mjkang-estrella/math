#!/usr/bin/env python3
"""Read-only artifact verifier. Does not execute payloads or prove mathematics."""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath

def sha(b):return hashlib.sha256(b).hexdigest()
def require(ok,msg):
    if not ok:raise ValueError(msg)
def safe(s):
    p=PurePosixPath(s)
    require(not p.is_absolute() and s==str(p) and '..' not in p.parts,'unsafe relative path')
    return p

def inventory(p):
    require(p.is_dir() and not p.is_symlink(),'bad packet root')
    files={};dirs={'.':stat.S_IMODE(p.stat().st_mode)}
    for base,ds,fs in os.walk(p,followlinks=False):
        for n in ds:
            q=Path(base)/n;st=q.lstat();rel=q.relative_to(p).as_posix()
            require(stat.S_ISDIR(st.st_mode) and not q.is_symlink(),'non-directory/symlink '+rel)
            dirs[rel]=stat.S_IMODE(st.st_mode)
        for n in fs:
            q=Path(base)/n;st=q.lstat();rel=q.relative_to(p).as_posix()
            require(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'nonregular/multiply-linked '+rel)
            files[rel]=dict(size=st.st_size,mode=stat.S_IMODE(st.st_mode),sha256=sha(q.read_bytes()))
    return files,dirs

def verify(root,anchors,original_project=None):
    require(root.is_dir() and not root.is_symlink(),'bad root')
    packet=root/'packet'
    for name,path in [('final',packet/'FINAL.json'),('manifest',packet/'MANIFEST.json'),('report',root/'REPORT.md')]:
        st=path.lstat();require(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and stat.S_IMODE(st.st_mode)==0o644,'bad seal/report type or mode')
        require(sha(path.read_bytes())==anchors[name],name+' detached hash mismatch')
    final=json.loads((packet/'FINAL.json').read_text());manifest=json.loads((packet/'MANIFEST.json').read_text())
    require(final['manifest_sha256']==anchors['manifest'] and final['outside_report_sha256']==anchors['report'],'internal seal binding mismatch')
    files,dirs=inventory(packet)
    for k in ['FINAL.json','MANIFEST.json']:files.pop(k)
    require(files==manifest['files'],'payload inventory/bytes/mode mismatch')
    require(dirs==manifest['directories'],'directory inventory/mode mismatch')
    for rel in files:safe(rel)
    tree_bytes=(packet/'private/context/preprints-tree.json').read_bytes()
    require(sha(tree_bytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','tree hash')
    tree=json.loads(tree_bytes);require(len(tree['tree'])==13223 and tree['truncated'] is False,'tree completeness metadata')
    index={e['path']:e for e in tree['tree']}
    receipts=json.loads((packet/'private/sources/acquisition.json').read_text())
    for e in receipts:
        rel=e['path'];safe(rel);b=(packet/'private/sources'/rel).read_bytes();t=index[rel]
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(len(b)==e['size']==t['size'] and blob==e['git_blob_sha1']==t['sha'] and sha(b)==e['sha256'],'pinned blob mismatch '+rel)
        require(e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+rel,'pinned URL')
    primaries=json.loads((packet/'private/primary/receipts.json').read_text())
    for e in primaries:
        if 'error' in e:continue
        b=(packet/'private/primary'/(e['version']+'.pdf')).read_bytes()
        require(b.startswith(b'%PDF') and len(b)==e['size'] and sha(b)==e['sha256'],'primary receipt mismatch')
    bindings=json.loads((packet/'private/context/bindings.json').read_text())
    for e in bindings:
        safe(e['copy']);b=(packet/e['copy']).read_bytes()
        require(len(b)==e['size'] and sha(b)==e['sha256'],'copied input binding')
        if original_project:
            safe(e['original']);require(sha((original_project/e['original']).read_bytes())==e['sha256'],'current named original changed: '+e['original'])
    scope=json.loads((packet/'private/support-scope-binding.json').read_text())
    require(sha((packet/scope['path']).read_bytes())==scope['sha256'],'supporting scope changed')
    return dict(label='artifact integrity only; no mathematical gate',payloads=len(files),directories=len(dirs),pinned_blobs=len(receipts),primary_pdfs=len(primaries),named_bindings=len(bindings),original_comparison=bool(original_project))

def main():
    a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True)
    for k in ['final','manifest','report']:a.add_argument('--'+k+'-sha256',required=True)
    a.add_argument('--original-project',type=Path);v=a.parse_args()
    try:print(json.dumps(verify(v.root,{k:getattr(v,k+'_sha256') for k in ['final','manifest','report']},v.original_project),sort_keys=True))
    except Exception as e:print(json.dumps(dict(error=str(e),label='artifact verification rejected')));raise SystemExit(1)
if __name__=='__main__':main()
