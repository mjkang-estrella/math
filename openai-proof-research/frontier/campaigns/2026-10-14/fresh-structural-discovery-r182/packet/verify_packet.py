"""Read-only artifact verification. Requires explicit detached anchors; no self-grading."""
import argparse, hashlib, json, os
from pathlib import Path, PurePosixPath

def sha(data): return hashlib.sha256(data).hexdigest()
def require(ok, message):
    if not ok: raise ValueError(message)
def anchored(path, expected):
    require(len(expected)==64 and all(c in '0123456789abcdef' for c in expected), 'invalid explicit SHA256')
    data=path.read_bytes(); require(sha(data)==expected, 'detached anchor mismatch: '+str(path)); return data

def validate(root, final_sha, manifest_sha, report_sha, project=None):
    final=json.loads(anchored(root/'FINAL.json',final_sha))
    manifest=json.loads(anchored(root/'packet/MANIFEST.json',manifest_sha))
    anchored(root/'REPORT.md',report_sha)
    require(final['manifest_sha256']==manifest_sha,'FINAL manifest binding mismatch')
    members=manifest['members']; expected=set(); base=root/'packet'
    for item in members:
        rel=item['path']; pp=PurePosixPath(rel)
        require(not pp.is_absolute() and '..' not in pp.parts and rel==pp.as_posix(),'unsafe manifest path')
        require(rel!='MANIFEST.json' and rel not in expected,'duplicate/self manifest member')
        expected.add(rel)
        path=base/rel; require(path.is_file() and not path.is_symlink(),'missing/nonregular member: '+rel)
        data=path.read_bytes();require(len(data)==item['bytes'] and sha(data)==item['sha256'],'member mismatch: '+rel)
    actual=set()
    for directory, dirs, files in os.walk(base,followlinks=False):
        for name in dirs+files:require(not (Path(directory)/name).is_symlink(),'symlink in packet')
        for name in files:actual.add((Path(directory)/name).relative_to(base).as_posix())
    require(actual==expected|{'MANIFEST.json'},'packet membership mismatch')
    if 'frozen_statement_sha256' in final:
        for path in [root/'FROZEN-THEOREM.md',base/'FROZEN-THEOREM.md']:
            require(sha(path.read_bytes())==final['frozen_statement_sha256'],'frozen bytes mismatch')
        for name, digest in final['working_notes'].items():
            require(sha((root/'notes'/name).read_bytes())==digest,'working note mismatch')
            require(sha((base/'notes'/name).read_bytes())==digest,'selected note mismatch')
    original_count=0
    if project is not None:
        rec=json.loads((base/'private/direct-anchors.json').read_text())['complete_tree']
        data=(project/rec['path']).read_bytes();require(len(data)==rec['bytes'] and sha(data)==rec['sha256'],'complete tree changed');original_count+=1
        for rec in json.loads((base/'private/completed-exceptions.json').read_text()):
            data=(project/rec['path']).read_bytes();require(len(data)==rec['bytes'] and sha(data)==rec['sha256'],'completed exception changed');original_count+=1
        for rec in json.loads((base/'private/history-extents.json').read_text()):
            data=(project/rec['path']).read_bytes();require(sha(data)==rec['original_sha256'],'selected original changed');original_count+=1
        tree=json.loads((base/'private/source-tree-selected.json').read_text())
        for rec in json.loads((base/'private/source-authentication.json').read_text()):
            data=(base/'private'/PurePosixPath(rec['path']).name).read_bytes()
            blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            entry=next(t for t in tree if t['path']==rec['path'])
            require(blob==rec['git_blob']==entry['sha'] and len(data)==entry['size'],'pinned Git binding mismatch')
    return {'artifact_only':'verified','members':len(members),'explicit_originals_checked':original_count}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True)
    p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True)
    p.add_argument('--project',type=Path)
    a=p.parse_args()
    try:print(json.dumps(validate(a.root,a.final_sha256,a.manifest_sha256,a.report_sha256,a.project),sort_keys=True))
    except (ValueError,OSError,KeyError,StopIteration) as e:p.exit(1,str(e)+'\n')
