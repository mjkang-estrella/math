#!/usr/bin/env python3
"""READ-ONLY exact-packet artifact verifier. No mathematical verdicts.
Explicit detached anchors are mandatory. No files are written by this program.
"""
import argparse, hashlib, json, os, re, stat
from pathlib import Path, PurePosixPath

RESERVED={'MANIFEST.json','REPORT.md','DETACHED.json','artifact-verification.json'}
def sha(b): return hashlib.sha256(b).hexdigest()
def require(ok,msg):
    if not ok: raise ValueError(msg)
def safe_name(s):
    p=PurePosixPath(s)
    return bool(s) and not p.is_absolute() and '..' not in p.parts and str(p)==s

def verify(root,final_anchor,manifest_anchor,report_anchor):
    root=Path(root)
    require(root.is_dir() and not root.is_symlink(),'root is not a regular directory')
    for name,anchor in [('FINAL.md',final_anchor),('MANIFEST.json',manifest_anchor),('REPORT.md',report_anchor)]:
        require(re.fullmatch('[0-9a-f]{64}',anchor) is not None,'malformed explicit anchor')
        p=root/name
        require(p.is_file() and not p.is_symlink(),'missing or linked anchored file: '+name)
        require(sha(p.read_bytes())==anchor,'detached anchor mismatch: '+name)
        require(stat.S_IMODE(p.stat().st_mode)==0o600,'anchored file mode mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_text())
    require(m['schema']=='r228-exact-local-selection-v1','unsupported schema')
    require(set(m['outside_manifest'])==RESERVED,'outside selection policy mismatch')
    entries=m['files']; dirs=m['directories']
    paths=[e['path'] for e in entries]
    require(len(paths)==len(set(paths)),'duplicate selected path')
    require(all(safe_name(p) and p not in RESERVED for p in paths),'unsafe selected path')
    require('FINAL.md' in paths,'FINAL not selected')
    actual_files=set();actual_dirs={'.'}
    require(stat.S_IMODE(root.stat().st_mode)==0o700,'root directory mode mismatch')
    for cur,dd,ff in os.walk(root,followlinks=False):
        for n in dd:
            p=Path(cur)/n
            require(not p.is_symlink(),'linked directory')
            actual_dirs.add(p.relative_to(root).as_posix())
        for n in ff:
            p=Path(cur)/n
            require(p.is_file() and not p.is_symlink(),'nonregular file')
            rel=p.relative_to(root).as_posix()
            if rel not in RESERVED:actual_files.add(rel)
    require(actual_files==set(paths),'exact selected file set mismatch')
    require(actual_dirs==set(dirs),'exact directory set mismatch')
    for d in dirs:
        require(d=='.' or safe_name(d),'unsafe directory path')
        require(stat.S_IMODE((root/d).stat().st_mode)==0o700,'directory mode mismatch: '+d)
    total=0
    for e in entries:
        p=root/e['path'];b=p.read_bytes();total+=len(b)
        require(len(b)==e['bytes'],'byte size mismatch: '+e['path'])
        require(sha(b)==e['sha256'],'selected hash mismatch: '+e['path'])
        require(e['mode']=='0600' and stat.S_IMODE(p.stat().st_mode)==0o600,'selected mode mismatch: '+e['path'])
    for name in RESERVED:
        p=root/name
        if p.exists(): require(stat.S_IMODE(p.stat().st_mode)==0o600,'outside artifact mode mismatch: '+name)
    return {'artifact_only':True,'selected_files':len(entries),'selected_bytes':total,'directories':len(dirs),'exact_selection_and_modes':'matched','explicit_detached_anchors':'matched','read_only':True}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True)
    ap.add_argument('--final-sha256',required=True);ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--report-sha256',required=True)
    a=ap.parse_args()
    try: print(json.dumps(verify(a.root,a.final_sha256,a.manifest_sha256,a.report_sha256),sort_keys=True))
    except (ValueError,KeyError,OSError,json.JSONDecodeError) as e:
        print(json.dumps({'artifact_only':True,'rejected':str(e)},sort_keys=True));raise SystemExit(1)
