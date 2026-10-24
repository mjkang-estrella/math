"""Read-only exact-selection verifier; detached hashes must be supplied explicitly."""
import argparse, hashlib, json, os, re, stat
from pathlib import Path, PurePosixPath

OUTSIDE={'MANIFEST.json','REPORT.md','ANCHORS.json','verification.json'}
SPECIAL_PRIVATE={'GUARDS.json','SESSION.md','SELECTION.json'}
def digest(b): return hashlib.sha256(b).hexdigest()
def mode(p): return format(stat.S_IMODE(p.lstat().st_mode),'04o')
def check_path(s):
    q=PurePosixPath(s)
    assert s and not q.is_absolute() and '..' not in q.parts and q.as_posix()==s, ('unsafe path',s)
    assert s not in OUTSIDE and q.parts[0]!='controls', ('outside selected payload',s)
    return q

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',required=True)
    for s in ['manifest','final','report']: ap.add_argument('--'+s+'-sha256',required=True)
    a=ap.parse_args(); root=Path(a.root).resolve()
    assert root==Path(__file__).resolve().parent, 'root must be this verifier copy directory'
    assert mode(root)=='0700', 'root directory mode'
    expected={k:getattr(a,k+'_sha256') for k in ['manifest','final','report']}
    for v in expected.values(): assert re.fullmatch('[0-9a-f]{64}',v), 'invalid explicit anchor'
    for k,name in [('manifest','MANIFEST.json'),('final','FINAL.md'),('report','REPORT.md')]:
        p=root/name
        assert stat.S_ISREG(p.lstat().st_mode) and not p.is_symlink(), ('nonregular anchor',name)
        assert digest(p.read_bytes())==expected[k], ('detached hash mismatch',name)
    assert mode(root/'MANIFEST.json')=='0400'
    assert mode(root/'REPORT.md')=='0444'
    m=json.loads((root/'MANIFEST.json').read_bytes())
    assert m['schema']=='r214-exact-selection-v1'
    entries=m['files']; names=[x['path'] for x in entries]
    assert names==sorted(set(names)), 'duplicate/unsorted manifest'
    for e in entries:
        q=check_path(e['path']);p=root.joinpath(*q.parts)
        for parent in [p,*p.parents]:
            if parent==root.parent: break
            assert not parent.is_symlink(), ('symlink',str(parent))
        assert stat.S_ISREG(p.lstat().st_mode), ('not a regular file',e['path'])
        b=p.read_bytes()
        assert len(b)==e['bytes'] and digest(b)==e['sha256'], ('payload mismatch',e['path'])
        wanted='0400' if e['path'].startswith('private/') or e['path'] in SPECIAL_PRIVATE else '0444'
        assert e['mode']==wanted and mode(p)==wanted, ('mode mismatch',e['path'])
        assert e['rights'] in ['original-local','private-original-rights','private-task-metadata']
    selection=json.loads((root/'SELECTION.json').read_bytes())
    assert selection['files']==names, 'manifest/selection mismatch'
    assert selection['outside_files']==sorted(OUTSIDE)
    assert selection['outside_directories']==['controls']
    actual=[];dirs=[]
    for base,sub,files in os.walk(root,followlinks=False):
        rel=Path(base).relative_to(root).as_posix()
        if rel=='.': sub[:]=[s for s in sub if s!='controls']
        for s in sub: assert not (Path(base)/s).is_symlink(), ('symlink directory',s)
        if rel!='.': dirs.append(rel)
        for s in files:
            q=(Path(base)/s).relative_to(root).as_posix()
            assert not (root/q).is_symlink(), ('symlink file',q)
            if q not in OUTSIDE: actual.append(q)
    assert sorted(actual)==names, {'missing':sorted(set(names)-set(actual)),'extra':sorted(set(actual)-set(names))}
    expected_dirs=sorted({p.as_posix() for name in names for p in PurePosixPath(name).parents if p.as_posix()!='.'})
    assert sorted(dirs)==expected_dirs, 'directory selection mismatch'
    assert m['directories']==[{'path':d,'mode':'0700'} for d in expected_dirs]
    for d in expected_dirs: assert mode(root/d)=='0700', ('directory mode',d)
    for name in ['ANCHORS.json','verification.json']:
        if (root/name).exists(): assert mode(root/name)=='0400', ('detached output mode',name)
    source_count=0
    if 'private/source-authentication.json' in names:
        records=json.loads((root/'private/source-authentication.json').read_bytes())
        for r in records:
            assert r['local'] in names
            b=(root/r['local']).read_bytes()
            blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            assert len(b)==r['bytes'] and digest(b)==r['sha256'] and blob==r['git_blob'], ('source changed',r['local'])
            source_count+=1
        assert source_count==14
    print(json.dumps({'artifact_only':True,'exact_selection':True,'selected_files':len(names),'selected_bytes':sum(e['bytes'] for e in entries),'hashes':True,'modes':True,'source_blobs_unchanged':source_count,'writes_performed':0,'anchors':expected},sort_keys=True))

if __name__=='__main__': main()
