"""Read-only exact-selection verifier. Requires independent FINAL/MANIFEST/REPORT anchors.
Artifact integrity only: no mathematical verification, writes, network, or subprocesses.
Run from project root with python -B.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, re, stat

def sha(b): return hashlib.sha256(b).hexdigest()
def require(test, why):
    if not test: raise ValueError(why)
def mode(p): return format(stat.S_IMODE(p.lstat().st_mode), '04o')
def regular(p):
    require(stat.S_ISREG(p.lstat().st_mode), 'not regular/non-symlink: '+str(p))
    return p.read_bytes()
def inventory(packet):
    require(stat.S_ISDIR(packet.lstat().st_mode), 'packet not real directory')
    files={}; dirs={'.':mode(packet)}
    for base,children,names in os.walk(packet, topdown=True, followlinks=False):
        base=Path(base)
        for name in children:
            p=base/name
            require(stat.S_ISDIR(p.lstat().st_mode),'non-directory or symlink: '+str(p))
            dirs[p.relative_to(packet).as_posix()]=mode(p)
        for name in names:
            p=base/name; b=regular(p); rel=p.relative_to(packet).as_posix()
            files[rel]={'path':rel,'bytes':len(b),'mode':mode(p),'sha256':sha(b)}
    return files,dirs

def verify(root,final_sha,manifest_sha,report_sha):
    require(stat.S_ISDIR(root.lstat().st_mode),'root not real directory')
    for h in (final_sha,manifest_sha,report_sha):
        require(re.fullmatch('[0-9a-f]{64}',h) is not None,'invalid anchor')
    mb=regular(root/'MANIFEST.json'); rb=regular(root/'REPORT.txt')
    require(sha(mb)==manifest_sha,'MANIFEST detached hash mismatch')
    require(sha(rb)==report_sha,'REPORT detached hash mismatch')
    require(mode(root/'MANIFEST.json')=='0444','MANIFEST mode mismatch')
    require(mode(root/'REPORT.txt')=='0444','REPORT mode mismatch')
    m=json.loads(mb)
    require(m['format']=='structural-r197-proof-r1-exact-selection-v1','unknown manifest format')
    expected={}
    for e in m['files']:
        p=PurePosixPath(e['path'])
        require(not p.is_absolute() and '..' not in p.parts and p.as_posix()==e['path'],'unsafe file path')
        require(e['path'] not in expected,'duplicate file')
        expected[e['path']]=e
    expected_dirs={}
    for e in m['directories']:
        p=PurePosixPath(e['path'])
        require(not p.is_absolute() and '..' not in p.parts and p.as_posix()==e['path'],'unsafe directory path')
        require(e['path'] not in expected_dirs,'duplicate directory')
        expected_dirs[e['path']]=e['mode']
    files,dirs=inventory(root/'packet')
    require(set(files)==set(expected),'exact file membership mismatch')
    require(dirs==expected_dirs,'exact directory membership/mode mismatch')
    for rel,e in expected.items(): require(files[rel]==e,'file bytes/hash/mode mismatch: '+rel)
    require(sha(regular(root/'packet/FINAL.txt'))==final_sha,'FINAL detached hash mismatch')
    pins={'private/frozen-inputs/STATEMENT.txt':'8030aa7c2a40a2b3cf5a3cfd6eacb6c78acd7984fad6d3ee0de7c3de2657537d',
          'private/frozen-inputs/AUTHOR-PROOF.txt':'8196eceec11a0b71f03dc4dd31744300dc3601a0c623ac2e1145d84ebf4d231e'}
    for rel,h in pins.items():
        if rel in files: require(files[rel]['sha256']==h,'frozen reviewed input mismatch')
    if 'private/reading-records.json' in files:
        reading=json.loads(regular(root/'packet/private/reading-records.json'))
        tree=json.loads(regular(root/'packet/private/source-tree.json'))
        blobs={e['path']:e for e in tree if e['type']=='blob'}
        require(len(tree)==13 and len(blobs)==10,'source tree selection mismatch')
        require(set(blobs)=={e['canonical_path'] for e in reading['source']},'source exact blob membership mismatch')
        for e in reading['source']:
            b=regular(root/'packet'/e['local_path'])
            git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            require(git==e['git_blob']==blobs[e['canonical_path']]['sha'],'source Git blob mismatch')
            require(len(b)==e['bytes']==blobs[e['canonical_path']]['size'] and sha(b)==e['sha256'],'source length/SHA mismatch')
    return {'artifact_verification':'PASS','files':len(files),'directories':len(dirs),'read_only':True,'mathematical_status':'not assessed'}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',required=True,type=Path)
    p.add_argument('--final-sha256',required=True)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    try: print(json.dumps(verify(a.root,a.final_sha256,a.manifest_sha256,a.report_sha256),sort_keys=True))
    except Exception as e:
        print(json.dumps({'artifact_verification':'FAIL','reason':str(e)},sort_keys=True)); raise SystemExit(1)
