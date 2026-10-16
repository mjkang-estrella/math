#!/usr/bin/env python3
"""Read-only integrity and exact finite replay, MIT, Myeongjin Kang.

Usage: python -I -B verify.py EXTERNAL_SEAL_SHA256 [CAMPAIGN_ROOT]
Do not derive the trusted anchor from this untrusted package itself.
No network, writes, regeneration, imports of historical code, or repairs.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import sys

PRIOR={
 'fresh-structural-discovery-r8':'6db6112bf4297450c063652b5cc415d8a4f2d20b8b5138753349fcbafbfd3600',
 'elementary-unimodality-r2':'6acd4f102adb468822a74642de8e43374ab10628e86d74d20f3c50c663cb55aa',
}
META={'inputs-manifest.json','outputs-manifest.json','seal.json','seal.sha256'}
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def sha(b):return hashlib.sha256(b).hexdigest()


def tree(root):
    if not root.is_dir():
        return {'__missing_directory__':str(root)}
    out={}
    for p in sorted(root.rglob('*')):
        rel=p.relative_to(root).as_posix()
        if p.is_symlink():
            out[rel]={'symlink':str(p.readlink())}
        elif p.is_file():
            b=p.read_bytes();out[rel]={'sha256':sha(b),'size':len(b)}
    return out


def safe(root,name):
    q=PurePosixPath(name)
    assert name and not q.is_absolute() and '..' not in q.parts and '.' not in q.parts
    assert q.as_posix()==name
    p=root.joinpath(*q.parts)
    assert not p.is_symlink() and p.is_file(), 'missing/nonregular member '+name
    return p


def authenticate(root,anchor):
    sb=safe(root,'seal.json').read_bytes()
    assert sha(sb)==anchor,'external seal mismatch'
    assert safe(root,'seal.sha256').read_text().strip().split()[0]==anchor,'detached seal file mismatch'
    seal=json.loads(sb)
    assert set(seal['manifests'])=={'inputs-manifest.json','outputs-manifest.json'}
    paths=[];counts={}
    for mn,meta in seal['manifests'].items():
        b=safe(root,mn).read_bytes()
        assert len(b)==meta['size'] and sha(b)==meta['sha256'],'manifest binding '+mn
        rows=json.loads(b)['files'];counts[mn]=len(rows)
        for r in rows:
            p=safe(root,r['path']);data=p.read_bytes()
            assert len(data)==r['size'] and sha(data)==r['sha256'],'member integrity '+r['path']
            paths.append(r['path'])
    assert len(paths)==len(set(paths)), 'duplicate manifest member'
    actual=tree(root)
    assert set(actual)==set(paths)|META,'exact membership mismatch'
    assert all('symlink' not in v for v in actual.values()),'symlink forbidden'
    return counts


BOOTSTRAP=r'''
import sys, os, runpy
def audit(event,args):
    if event=='open':
        mode=args[1]; flags=args[2]
        if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise RuntimeError('READ_ONLY_AUDIT_REJECTED_WRITE')
    if event.startswith(('socket.','subprocess.','ctypes.')) or event in {
        'os.remove','os.rename','os.rmdir','os.mkdir','os.link','os.symlink',
        'os.chmod','os.chown','os.truncate','os.utime','os.system','os.exec',
        'os.posix_spawn','os.fork','shutil.copyfile','shutil.copymode','shutil.copystat'}:
        raise RuntimeError('READ_ONLY_AUDIT_REJECTED_'+event)
sys.addaudithook(audit)
sys.argv=[sys.argv[1]]
runpy.run_path(sys.argv[0],run_name='__main__')
'''


def main():
    assert len(sys.argv) in (2,3),'supply externally pinned seal SHA256'
    anchor=sys.argv[1]
    assert len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor)
    root=Path(__file__).resolve().parent
    campaign=Path(sys.argv[2]).resolve() if len(sys.argv)==3 else root.parent
    roots=[root]+[campaign/name for name in PRIOR]
    before=[tree(p) for p in roots]
    report=None
    try:
        counts=authenticate(root,anchor)
        prior_counts={}
        for name,h in PRIOR.items():
            original=campaign/name
            prior_counts[name]=authenticate(original,h)
            copied=root/'inputs/private/continuity'/name
            for fname in ['seal.json','seal.sha256','inputs-manifest.json','outputs-manifest.json',
                          'candidate.md','source-contracts.md','original-scope.md']:
                assert safe(copied,fname).read_bytes()==safe(original,fname).read_bytes(), 'continuity copy mismatch'
        upstream=json.loads(safe(root,'inputs/private/context/sources/upstream.json').read_text())
        assert upstream['commit']==PIN
        full_tree=json.loads(safe(root,'inputs/private/context/sources/preprints-tree.json').read_text())
        assert full_tree.get('truncated',False) is False
        entries={e['path']:e for e in full_tree['tree'] if e['type']=='blob'}
        pins=json.loads(safe(root,'inputs/upstream-pins.json').read_text())
        assert len(pins)==25
        for pin in pins:
            b=safe(root,pin['path']).read_bytes();p=pin['upstream_path']
            git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            assert git==pin['git_blob_sha1']==entries[p]['sha']
            assert len(b)==pin['size'] and sha(b)==pin['sha256']
            assert pin['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+p
        replay={}
        # All package members and original continuity trees are authenticated
        # BEFORE any stored checker code runs. No prior code is executed.
        for script,receipt in [('tate_checks.py','checks-receipt.json'),
                               ('relative_probe.py','probe-receipt.json'),
                               ('operations_checks.py','operations-receipt.json')]:
            result=subprocess.run([sys.executable,'-I','-B','-c',BOOTSTRAP,str(safe(root,script))],
                                  cwd=root,capture_output=True,timeout=60)
            assert result.returncode==0,'checker failure '+script+': '+result.stderr.decode(errors='replace')[-1500:]
            assert not result.stderr,'unexpected checker stderr '+script
            assert result.stdout==safe(root,receipt).read_bytes(),'receipt mismatch '+script
            replay[script]=sha(result.stdout)
        report={'status':'PASS_INTEGRITY_AND_EXACT_FINITE_SUPPORT_ONLY_C_UNRESOLVED',
                'seal_sha256':anchor,'counts':counts,'pinned_git_blobs':len(pins),
                'prior_inventory_counts':prior_counts,'replay_stdout_sha256':replay,
                'whole_trees_unchanged':True,'independent_mathematical_review':False,
                'counted':False}
    finally:
        after=[tree(p) for p in roots]
        assert before==after,'FROZEN_TREE_CHANGED_ON_SUCCESS_OR_FAILURE'
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__=='__main__':main()
