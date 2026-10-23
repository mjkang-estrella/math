#!/usr/bin/env python3
"""Read-only exact-selection verifier. This verifies artifacts, never mathematics.
Pass all three detached anchors explicitly; no anchor is trusted merely because
it occurs in a file inside the packet. Run with python -B.
"""
import argparse,hashlib,json,os,re,stat,sys
from pathlib import Path,PurePosixPath

def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        while True:
            b=f.read(1024*1024)
            if not b:break
            h.update(b)
    return h.hexdigest()

def mode(path):return format(stat.S_IMODE(path.lstat().st_mode),'04o')

def safe(rel):
    p=PurePosixPath(rel)
    if not isinstance(rel,str) or not rel or p.is_absolute() or '..' in p.parts or '\\' in rel or p.as_posix()!=rel:
        raise ValueError('unsafe/noncanonical relative path')
    return rel

def verify(a):
    root=Path(a.root).resolve(strict=True)
    for value in (a.final_sha256,a.manifest_sha256,a.report_sha256):
        if not re.fullmatch('[0-9a-f]{64}',value):raise ValueError('explicit SHA256 anchors required')
    mp=root/'MANIFEST.json'
    if mp.is_symlink() or digest(mp)!=a.manifest_sha256:raise ValueError('MANIFEST detached anchor mismatch')
    m=json.loads(mp.read_text())
    if m.get('schema')!='r199-exact-selection-v1':raise ValueError('manifest schema mismatch')
    final=safe(m['final_path']);report=safe(m['report_path'])
    if (root/final).is_symlink() or digest(root/final)!=a.final_sha256:raise ValueError('FINAL detached anchor mismatch')
    if (root/report).is_symlink() or digest(root/report)!=a.report_sha256:raise ValueError('REPORT detached anchor mismatch')
    rows=m['files'];selected={}
    for row in rows:
        rel=safe(row['path'])
        if rel in selected:raise ValueError('duplicate selected path')
        selected[rel]=row
    if len({x.casefold() for x in selected})!=len(selected):raise ValueError('casefold path collision')
    outside={safe(x) for x in m['outside_selection_files']}
    prefixes=[safe(x.rstrip('/'))+'/' for x in m['outside_selection_prefixes']]
    if final not in selected or report not in outside or set(selected)&outside:raise ValueError('selection/anchor roles mismatch')
    if 'MANIFEST.json' not in outside:raise ValueError('manifest must be detached from selected files')
    def omitted(rel):return any(rel==p[:-1] or rel.startswith(p) for p in prefixes)
    if any(omitted(x) for x in selected):raise ValueError('selected file under omitted prefix')
    actual_files=set();actual_dirs={'.'}
    for current,dirs,files in os.walk(root,topdown=True,followlinks=False):
        keep=[]
        for name in dirs:
            path=Path(current)/name;rel=path.relative_to(root).as_posix()
            if omitted(rel):continue
            if path.is_symlink():raise ValueError('symlink directory '+rel)
            actual_dirs.add(rel);keep.append(name)
        dirs[:]=keep
        for name in files:
            path=Path(current)/name;rel=path.relative_to(root).as_posix()
            if omitted(rel):continue
            if path.is_symlink():raise ValueError('symlink file '+rel)
            actual_files.add(rel)
    if actual_files!=set(selected)|outside:
        raise ValueError('exact file selection mismatch: missing='+str(sorted((set(selected)|outside)-actual_files))+' extra='+str(sorted(actual_files-(set(selected)|outside))))
    dir_rows=m['directories'];expected_dirs={x['path']:x['mode'] for x in dir_rows}
    if len(expected_dirs)!=len(dir_rows) or set(expected_dirs)!=actual_dirs:raise ValueError('exact directory selection mismatch')
    for rel,expected_mode in expected_dirs.items():
        if rel!='.':safe(rel)
        if mode(root/rel)!=expected_mode:raise ValueError('directory mode mismatch '+rel)
    if set(m['outside_selection_modes'])!=outside:raise ValueError('detached mode selection mismatch')
    for rel,expected_mode in m['outside_selection_modes'].items():
        if mode(root/rel)!=expected_mode:raise ValueError('detached file mode mismatch '+rel)
    for rel,row in selected.items():
        path=root/rel
        if not path.is_file():raise ValueError('not a regular file '+rel)
        if mode(path)!=row['mode']:raise ValueError('file mode mismatch '+rel)
        if path.stat().st_size!=row['bytes']:raise ValueError('byte length mismatch '+rel)
        if digest(path)!=row['sha256']:raise ValueError('content hash mismatch '+rel)
    return {'artifact_verification':'OK','selected_files':len(selected),'selected_directories':len(expected_dirs),'mathematical_verdict':None}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',required=True)
    p.add_argument('--final-sha256',required=True)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--report-sha256',required=True)
    args=p.parse_args()
    try:print(json.dumps(verify(args),sort_keys=True))
    except Exception as e:
        print(json.dumps({'artifact_verification':'REJECT','reason':str(e),'mathematical_verdict':None},sort_keys=True))
        sys.exit(1)
