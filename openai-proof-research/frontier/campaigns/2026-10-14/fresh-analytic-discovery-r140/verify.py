#!/usr/bin/env python3
"""Read-only exact packet verifier. Supply all three externally held SHA256s."""
from pathlib import Path
import argparse, hashlib, json, os, stat, gzip, io, tarfile
OUTSIDE={'MANIFEST.json','FINAL.md','REPORT.md'}
def digest(b): return hashlib.sha256(b).hexdigest()
def inventory(root):
    files={};dirs=[]
    for current,children,names in os.walk(root,followlinks=False):
        for name in children+names:
            p=Path(current)/name;st=p.lstat();rel=p.relative_to(root).as_posix()
            if stat.S_ISLNK(st.st_mode): raise ValueError('link: '+rel)
            if stat.S_ISDIR(st.st_mode):dirs.append(rel)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink!=1:raise ValueError('hardlink: '+rel)
                b=p.read_bytes();files[rel]={'size':len(b),'sha256':digest(b)}
            else:raise ValueError('nonregular: '+rel)
    return files,sorted(dirs)
def verify(root,anchors):
    root=Path(root).resolve()
    if set(anchors)!=OUTSIDE:raise ValueError('three explicit detached anchors required')
    for name in sorted(OUTSIDE):
        if digest((root/name).read_bytes())!=anchors[name]:raise ValueError('detached anchor: '+name)
    m=json.loads((root/'MANIFEST.json').read_bytes())
    if m['outside']!=sorted(OUTSIDE):raise ValueError('outside schema')
    files,dirs=inventory(root)
    if set(files)!=set(m['files'])|OUTSIDE:raise ValueError('file membership')
    if dirs!=m['directories']:raise ValueError('directory membership')
    for name,rec in m['files'].items():
        if files[name]!=rec:raise ValueError('payload: '+name)
    # Optional typed evidence in a real packet; controls need not contain it.
    if (root/'source-authentication.json').exists():
        source=json.loads((root/'source-authentication.json').read_bytes())
        selected=json.loads((root/'private/selected-source-tree.json').read_bytes())
        tree={x['path']:x for x in selected['tree']}
        if source['pin']!='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb':raise ValueError('pin')
        if source['tree_sha256']!='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b':raise ValueError('tree anchor')
        if source['entries']!=13223:raise ValueError('complete tree count')
        if set(tree)!={x['path'] for x in source['files']}:raise ValueError('selected source membership')
        for x in source['files']:
            b=(root/x['local']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            if blob!=x['gitblob'] or blob!=tree[x['path']]['sha'] or len(b)!=tree[x['path']]['size'] or digest(b)!=x['sha256']:raise ValueError('source binding')
        for primary in json.loads((root/'primary-authentication.json').read_bytes()):
            if 'raw' not in primary:continue
            raw=(root/primary['raw']).read_bytes()
            if len(raw)!=primary['size'] or digest(raw)!=primary['sha256']:raise ValueError('primary raw')
            members=primary.get('members',[])
            decoded=gzip.decompress(raw) if raw[:2]==b'\x1f\x8b' else raw
            if len(members)==1 and decoded.lstrip().startswith(b'\\pdfoutput'):
                if (root/members[0]['path']).read_bytes()!=decoded:raise ValueError('single tex recovery')
            elif members:
                with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
                    archive_bytes={t.name:archive.extractfile(t).read() for t in archive.getmembers() if t.isfile()}
                    for member in members:
                        rel=member['path'].split(primary['id']+'/',1)[1]
                        if archive_bytes.get(rel)!=(root/member['path']).read_bytes():raise ValueError('primary archive member')
            for member in members:
                b=(root/member['path']).read_bytes()
                if len(b)!=member['size'] or digest(b)!=member['sha256']:raise ValueError('primary member hash')
        for x in json.loads((root/'selected-copy-membership.json').read_bytes()):
            b=(root/x['path']).read_bytes()
            if len(b)!=x['size'] or digest(b)!=x['sha256']:raise ValueError('selected copy')
    return {'payload_files':len(m['files']),'outside_files':3,'directories':len(dirs),'status':'byte integrity only'}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',default=str(Path(__file__).resolve().parent));p.add_argument('--manifest',required=True);p.add_argument('--final',required=True);p.add_argument('--report',required=True);a=p.parse_args()
    print(json.dumps(verify(a.root,{'MANIFEST.json':a.manifest,'FINAL.md':a.final,'REPORT.md':a.report}),sort_keys=True))
