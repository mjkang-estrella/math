#!/usr/bin/env python3
"""Read-only local archive verifier. A detached manifest hash is mandatory."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
SCOPE='3cc7fd97d178dcf1e91a619d4873da74194ddf446afda79f479f5fa6fd1051b2'

def require(ok,message):
    if not ok: raise ValueError(message)

def sha(data): return hashlib.sha256(data).hexdigest()

def safe_path(base,name):
    rel=PurePosixPath(name)
    require(not rel.is_absolute() and str(rel)==name and '..' not in rel.parts and name not in ('','.'),'unsafe path')
    out=base.joinpath(*rel.parts)
    cursor=out
    while cursor!=base:
        require(not cursor.is_symlink(),'symlink: '+name)
        cursor=cursor.parent
    return out

def inventory(base,records,dirs,exclude=()):
    require(len(records)==len({x['path'] for x in records}),'duplicate file record')
    expected={x['path']:x for x in records}
    actual=set(); actual_dirs=set()
    for p in base.rglob('*'):
        rel=p.relative_to(base).as_posix()
        require(not p.is_symlink(),'symlink: '+rel)
        if p.is_file():
            if rel not in exclude: actual.add(rel)
        elif p.is_dir(): actual_dirs.add(rel)
        else: raise ValueError('nonregular member: '+rel)
    require(actual==set(expected),'exact file membership differs')
    require(actual_dirs==set(dirs) and len(dirs)==len(set(dirs)),'exact directory membership differs')
    for name,row in expected.items():
        b=safe_path(base,name).read_bytes()
        require(len(b)==row['bytes'] and sha(b)==row['sha256'],'file hash/size differs: '+name)

def verify(base,repo,anchor):
    require(re.fullmatch('[0-9a-f]{64}',anchor) is not None,'invalid detached SHA256')
    manifest_path=safe_path(base,'MANIFEST.json')
    raw=manifest_path.read_bytes()
    require(sha(raw)==anchor,'detached manifest anchor differs')
    m=json.loads(raw)
    require(m['pin']==PIN and m['status']=='UNRESOLVED' and m['nomination'] is False,'manifest scope/status differs')
    inventory(base,m['files'],m['directories'],exclude=('MANIFEST.json',))
    for row in m['external_anchors']:
        b=safe_path(repo,row['path']).read_bytes()
        require(len(b)==row['bytes'] and sha(b)==row['sha256'],'external anchor differs: '+row['path'])
    tree=json.loads(safe_path(repo,'sources/preprints-tree.json').read_bytes())
    require(tree['truncated'] is False and len(tree['tree'])==13223,'complete source tree contract differs')
    entries={r['path']:r for r in tree['tree']}
    require(len(entries)==13223,'duplicate complete-tree paths')
    require(json.loads(safe_path(repo,'sources/upstream.json').read_bytes())['commit']==PIN,'upstream pin differs')
    sources=json.loads(safe_path(base,'source-receipts.json').read_bytes())
    require(len(sources)==40 and len({r['path'] for r in sources})==40,'source membership differs')
    for row in sources:
        b=safe_path(base,row['local']).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(entries[row['path']]['type']=='blob' and entries[row['path']]['sha']==row['git_blob']==blob,'Git blob mismatch')
        require(sha(b)==row['sha256'] and len(b)==row['bytes'],'source receipt mismatch')
        require(row['raw_url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+row['path'],'nonpinned raw URL')
    for row in json.loads(safe_path(base,'primary-receipts.json').read_bytes()):
        require(sha(safe_path(base,row['local']).read_bytes())==row['sha256'],'primary PDF mismatch')
        text_path=str(PurePosixPath(row['local']).with_suffix('.txt'))
        require(sha(safe_path(base,text_path).read_bytes())==row['text_sha256'],'primary text mismatch')
    require(sha(safe_path(base,'public/scope-freeze.md').read_bytes())==SCOPE,'frozen scope changed')
    status=json.loads(safe_path(base,'status.json').read_bytes())
    require(status['target']=='T111I110' and status['status']=='UNRESOLVED' and status['nomination'] is False and status['count_credit']==0,'status disagrees')
    return {'integrity':'verified; not mathematical proof','manifest_sha256':anchor,
            'files':len(m['files']),'directories':len(m['directories']),
            'source_blobs':len(sources),'external_anchors':len(m['external_anchors']),
            'target':'T111I110','status':'UNRESOLVED','count_credit':0}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-sha256',required=True)
    parser.add_argument('--repository',type=Path,default=Path(__file__).resolve().parents[5])
    args=parser.parse_args()
    base=Path(__file__).resolve().parents[1]
    print(json.dumps(verify(base,args.repository.resolve(),args.manifest_sha256),indent=2))

if __name__=='__main__':
    try: main()
    except (OSError,ValueError,KeyError,TypeError) as exc:
        print('VERIFICATION FAILED: '+str(exc),file=sys.stderr)
        sys.exit(1)
