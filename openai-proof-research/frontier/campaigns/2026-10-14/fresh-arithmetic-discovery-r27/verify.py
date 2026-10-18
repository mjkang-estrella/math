#!/usr/bin/env python3
"""MIT; author Myeongjin Kang. Read-only identity checks, not proof certification."""
import argparse, hashlib, json, os, stat
from pathlib import Path

def sha(b): return hashlib.sha256(b).hexdigest()
def main():
    a=argparse.ArgumentParser(); a.add_argument('--expected',required=True);a.add_argument('--repo');q=a.parse_args()
    root=Path(__file__).resolve().parent
    manifest=root/'manifest.json'; data=manifest.read_bytes()
    assert sha(data)==q.expected, 'external manifest anchor mismatch'
    spec=json.loads(data); files={}; dirs=[]
    for base,ds,fs in os.walk(root,followlinks=False):
        for name in ds+fs:
            f=Path(base)/name;rel=f.relative_to(root).as_posix();s=f.lstat()
            assert not stat.S_ISLNK(s.st_mode), 'symlink: '+rel
            assert stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode), 'special file: '+rel
            if rel=='private' or rel.startswith('private/'):continue
            if stat.S_ISDIR(s.st_mode):dirs.append(rel)
            elif rel!='manifest.json':files[rel]={'sha256':sha(f.read_bytes()),'bytes':s.st_size}
    assert files==spec['files'],'public file inventory/hash mismatch'
    assert sorted(dirs)==spec['directories'],'public directory inventory mismatch'
    status=json.loads((root/'status.json').read_text()); assert status['status']=='NO_NOMINEE_PRE_FREEZE_SCREEN' and status['target_frozen'] is False and status['count']==13
    receipts=[]
    for f in ('receipts.json','receipts-319.json','receipts-companion.json'):receipts+=json.loads((root/f).read_text())
    assert len(receipts)==54 and len({r['path'] for r in receipts})==54
    actual=0
    for r in receipts:
        blob=r.get('git_blob_sha1',r.get('git_blob')); f=root/'private'/r['path'].removeprefix('preprints/')
        assert r['url']=='https://raw.githubusercontent.com/openai/math/'+spec['pin']+'/'+r['path']
        if f.exists():
            b=f.read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob;actual+=1
    canonical=0
    if q.repo:
        repo=Path(q.repo);tree=json.loads((repo/'sources/preprints-tree.json').read_text())['tree'];lookup={r['path']:r for r in tree}
        families={r['path'].split('/')[1] for r in receipts}
        expected={r['path'] for r in tree if r['type']=='blob' and r['path'].split('/')[1] in families and not r['path'].endswith('.pdf')}
        assert expected=={r['path'] for r in receipts}
        for r in receipts:assert lookup[r['path']]['sha']==r.get('git_blob_sha1',r.get('git_blob'));canonical+=1
    for r in json.loads((root/'primary-receipts.json').read_text()):
        f=root/'private/LP-v3.html'
        if f.exists():assert sha(f.read_bytes())==r['sha256'] and f.stat().st_size==r['bytes']
    print(json.dumps({'status':'PASS','public_files':len(files),'source_receipts':len(receipts),'private_source_bytes_checked':actual,'canonical_tree_blobs_checked':canonical,'mathematics_certified':False}))
if __name__=='__main__':main()
