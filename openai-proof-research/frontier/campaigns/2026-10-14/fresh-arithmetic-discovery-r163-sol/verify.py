#!/usr/bin/env python3
"""Read-only exact packet verifier. Artifact integrity, not mathematics."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

DETACHED = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
SOURCE_PREFIX = 'preprints/A-power-saving-for-planar-halving-lines-September-25-2026'
EXCEPTIONS = [
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162ct-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct/private/COMPARISON.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct/WORKLOG.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct/FINAL.md',
]
def digest(b): return hashlib.sha256(b).hexdigest()
def fail_if(condition, message):
    if condition: raise ValueError(message)
def safe(name, allow_dot=False):
    p=PurePosixPath(name)
    fail_if((name=='.' and not allow_dot) or p.is_absolute() or '..' in p.parts or '\\' in name or str(p)!=name, 'unsafe path '+name)
    return name

def collect(root):
    files=[]; dirs=[]
    fail_if(not stat.S_ISDIR(root.lstat().st_mode), 'root not directory')
    for base, names, leaves in os.walk(root, followlinks=False):
        names.sort();leaves.sort();p=Path(base);rel=p.relative_to(root).as_posix()
        st=p.lstat();fail_if(not stat.S_ISDIR(st.st_mode),'non-directory')
        dirs.append({'path':rel,'mode':st.st_mode})
        for n in names:
            fail_if(not stat.S_ISDIR((p/n).lstat().st_mode),'non-directory or symlink')
        for n in leaves:
            f=p/n; name=f.relative_to(root).as_posix();safe(name)
            st=f.lstat();fail_if(not stat.S_ISREG(st.st_mode),'non-regular '+name)
            if rel=='.' and n in DETACHED:continue
            b=f.read_bytes();files.append({'path':name,'mode':st.st_mode,'bytes':len(b),'sha256':digest(b)})
    return sorted(files,key=lambda x:x['path']),sorted(dirs,key=lambda x:x['path'])

def verify_payload(root, manifest):
    fail_if(manifest.get('pin')!=PIN,'pin')
    for field in ['files','directories']:
        rows=manifest[field];names=[r['path'] for r in rows]
        fail_if(names!=sorted(names) or len(names)!=len(set(names)),'ordering/duplicates '+field)
        for name in names:safe(name, field=='directories')
    f,d=collect(root)
    fail_if(f!=manifest['files'],'payload membership/bytes/modes')
    fail_if(d!=manifest['directories'],'directory membership/modes')
    return len(f),sum(x['bytes'] for x in f),len(d)

def git_blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def git_tree(path):
    items=[]
    for p in path.iterdir():
        st=p.lstat()
        if stat.S_ISDIR(st.st_mode):mode='40000';sha=git_tree(p);key=p.name.encode()+b'/'
        elif stat.S_ISREG(st.st_mode):
            fail_if(stat.S_IMODE(st.st_mode)!=0o644,'source mode')
            mode='100644';sha=git_blob(p.read_bytes());key=p.name.encode()
        else:raise ValueError('source type')
        items.append((key,mode.encode()+b' '+p.name.encode()+b'\0'+bytes.fromhex(sha)))
    b=b''.join(v for _,v in sorted(items))
    return hashlib.sha1(b'tree '+str(len(b)).encode()+b'\0'+b).hexdigest()

def verify_bindings(root, project):
    upstream=json.loads((root/'private/upstream.json').read_text())
    fail_if(upstream['commit']!=PIN,'upstream pin')
    raw=(root/'private/preprints-tree.json').read_bytes();fail_if(digest(raw)!=TREE_SHA256,'complete tree hash')
    tree=json.loads(raw);fail_if(tree['truncated'] or len(tree['tree'])!=13223,'complete tree shape')
    expected=[e for e in tree['tree'] if e['path']==SOURCE_PREFIX or e['path'].startswith(SOURCE_PREFIX+'/')]
    rows=json.loads((root/'private/SOURCE-BINDINGS.json').read_text())
    fail_if([r['path'] for r in rows]!=sorted(r['path'] for r in rows),'source order')
    fail_if({r['path'] for r in rows}!={e['path'] for e in expected},'source membership')
    lookup={e['path']:e for e in expected}
    for row in rows:
        e=lookup[row['path']]
        fail_if(any(row[k]!=v for k,v in e.items()),'source tree binding')
        rel=row['path'][len(SOURCE_PREFIX):].lstrip('/')
        path=root/'private/source'/rel
        if row['type']=='tree':fail_if(git_tree(path)!=row['sha'],'source git tree')
        else:
            b=path.read_bytes();fail_if(len(b)!=row['size'] or git_blob(b)!=row['sha'] or digest(b)!=row['sha256'],'source blob')
            fail_if(row['local']!=path.relative_to(root).as_posix(),'source local path')
    copies=json.loads((root/'private/EXCEPTION-BINDINGS.json').read_text())
    fail_if([r['original'] for r in copies]!=EXCEPTIONS,'exact exception allowlist')
    for r in copies:
        safe(r['original']);safe(r['copy'])
        for p in [project/r['original'],root/r['copy']]:
            st=p.lstat();fail_if(st.st_mode!=r['full_mode'] or not stat.S_ISREG(st.st_mode),'exception full mode')
            b=p.read_bytes();fail_if(len(b)!=r['bytes'] or digest(b)!=r['sha256'],'exception original/copy')
    return len([r for r in rows if r['type']=='blob']),len(rows),len(copies)

def check_anchor(path, expected):
    fail_if(len(expected)!=64 or any(c not in '0123456789abcdef' for c in expected),'bad anchor format')
    fail_if(digest(path.read_bytes())!=expected,'detached anchor '+path.name)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--project',type=Path,required=True)
    for label in ['final','manifest','report']:ap.add_argument('--'+label+'-sha256',required=True)
    a=ap.parse_args();root=a.root
    for name,value in [('FINAL.md',a.final_sha256),('MANIFEST.json',a.manifest_sha256),('REPORT.md',a.report_sha256)]:check_anchor(root/name,value)
    manifest=json.loads((root/'MANIFEST.json').read_text());counts=verify_payload(root,manifest);bound=verify_bindings(root,a.project)
    report=(root/'REPORT.md').read_text()
    fail_if(a.final_sha256 not in report or a.manifest_sha256 not in report,'report bindings')
    anchors=json.loads((root/'ANCHORS.json').read_text())
    fail_if(anchors!={'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256},'detached anchors file')
    print('MATCH payload_files=%d bytes=%d directories=%d source_blobs=%d source_entries=%d exact_copies=%d'%(*counts,*bound))
if __name__=='__main__':main()
