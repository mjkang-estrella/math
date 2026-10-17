#!/usr/bin/env python3
"""Read-only exact-membership verification of independent review bytes. MIT.
Requires an external anchor; does not rebuild Lean or establish mathematics.
"""
import argparse,hashlib,json,os,re,stat
from pathlib import Path,PurePosixPath

def require(ok,why):
    if not ok: raise ValueError(why)
def unique(pairs):
    out={}
    for k,v in pairs:
        require(k not in out,'duplicate JSON key'); out[k]=v
    return out
def safe(s):
    require(isinstance(s,str) and s and '\\' not in s,'bad path')
    p=PurePosixPath(s)
    require(not p.is_absolute() and p.as_posix()==s and all(x not in ('.','..','') for x in p.parts),'unsafe path')
    return s
def verify(root,anchor):
    require(re.fullmatch('[0-9a-f]{64}',anchor) is not None,'bad external anchor')
    require(root.is_dir() and not root.is_symlink(),'bad root')
    mp=root/'review-manifest.json'; require(not mp.is_symlink(),'manifest symlink')
    raw=mp.read_bytes(); require(hashlib.sha256(raw).hexdigest()==anchor,'external anchor mismatch')
    m=json.loads(raw,object_pairs_hook=unique)
    require(m['schema']=='O217-independent-manuscript-review-r1' and m['verdict']=='PASS_FULL_MANUSCRIPT_O217','schema/verdict')
    require(m['full_O217_theorem_formalized'] is False,'scope')
    rows={}
    for row in m['files']:
        p=safe(row['path']); require(p not in rows and p!='review-manifest.json','duplicate/self path')
        require(re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None,'bad digest'); rows[p]=row
    dirs=[safe(s) for s in m['directories']]; require(len(set(dirs))==len(dirs),'duplicate directories')
    actual_files=set(); actual_dirs=set()
    for base,ds,fs in os.walk(root,followlinks=False):
        for name in ds+fs:
            p=Path(base)/name; rel=safe(p.relative_to(root).as_posix()); mode=p.lstat().st_mode
            require(not stat.S_ISLNK(mode),'symlink '+rel)
            if stat.S_ISDIR(mode): actual_dirs.add(rel)
            else:
                require(stat.S_ISREG(mode),'nonregular '+rel); actual_files.add(rel)
    require(actual_files==set(rows)|{'review-manifest.json'},'exact file membership')
    require(actual_dirs==set(dirs),'exact directory membership')
    for name,row in rows.items():
        data=(root/name).read_bytes()
        require(len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'],'payload mismatch '+name)
    return {'result':'PASS_INTEGRITY_ONLY','files':len(rows),'directories':len(dirs),'writes':0,'mathematics_certified_by_hash':False}
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--anchor',required=True); p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent); a=p.parse_args()
    try: print(json.dumps(verify(a.root.absolute(),a.anchor),sort_keys=True))
    except (ValueError,KeyError,TypeError,OSError) as e:
        print('INTEGRITY_REJECT: '+str(e)); raise SystemExit(1)
