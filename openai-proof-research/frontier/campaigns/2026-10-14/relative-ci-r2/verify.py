#!/usr/bin/env python3
"""Read-only integrity/replay verifier. Original code MIT, Myeongjin Kang.
An external seal hash is mandatory. No imports of checker/local modules.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

R10_ANCHOR='ab76359004bde5f7615f04fc4d7893c4ede636cc5be22238b7521ca565fd679c'
META={'inputs-manifest.json','outputs-manifest.json','seal.json','seal.sha256'}

def record(path):
    b=path.read_bytes()
    return {'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}

def inventory(path):
    ans={}
    assert path.is_dir(), ('missing directory',str(path))
    for p in sorted(path.rglob('*')):
        assert not p.is_symlink(), ('symlink not permitted',str(p))
        if p.is_file():
            ans[str(p.relative_to(path))]=record(p)
    return ans

def authenticate_package(path,anchor):
    assert len(anchor)==64 and record(path/'seal.json')['sha256']==anchor, 'external anchor mismatch'
    detached=(path/'seal.sha256').read_text().split()
    assert detached in ([anchor],[anchor,'seal.json']), 'detached seal inconsistent'
    seal=json.loads((path/'seal.json').read_bytes())
    names=set(); counts={}
    for mn in ('inputs-manifest.json','outputs-manifest.json'):
        expected=seal['manifests'][mn]
        assert record(path/mn)=={k:expected[k] for k in ('size','sha256')}, ('manifest authentication',mn)
        entries=json.loads((path/mn).read_bytes())['files']; counts[mn]=len(entries)
        for e in entries:
            rel=Path(e['path'])
            assert not rel.is_absolute() and '..' not in rel.parts and e['path'] not in names, 'invalid or duplicate member'
            names.add(e['path'])
            assert record(path/rel)=={k:e[k] for k in ('size','sha256')}, ('payload authentication',e['path'])
    assert set(inventory(path))==names|META, 'exact package membership mismatch'
    return counts

def external_inventory(project,baseline):
    ans={}
    for e in baseline['r10']+baseline['continuity_and_context']:
        p=project/e['path']
        assert p.is_file() and not p.is_symlink(), ('missing/linked external file',e['path'])
        ans[e['path']]=record(p)
    r10=project/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r10'
    actual=inventory(r10)
    expected={str(Path(e['path']).relative_to(r10.relative_to(project))):{k:e[k] for k in ('size','sha256')} for e in baseline['r10']}
    assert actual==expected,'external r10 full tree mismatch'
    for e in baseline['continuity_and_context']:
        assert ans[e['path']]=={k:e[k] for k in ('size','sha256')},('external context mismatch',e['path'])
    return ans

def check_pins(project):
    r10=project/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r10'
    pins=json.loads((r10/'inputs/upstream-pins.json').read_bytes())
    preprints=json.loads((project/'sources/preprints-tree.json').read_bytes())
    bypath={e['path']:e for e in preprints['tree']}
    for e in pins:
        b=(r10/e['path']).read_bytes()
        assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
        git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert git==e['git_blob_sha1']==bypath[e['upstream_path']]['sha'],('Git pin mismatch',e['upstream_path'])
    return len(pins)

BOOTSTRAP=r'''
import sys,runpy
sys.dont_write_bytecode=True
def deny(event,args):
    if event=='open':
        mode=args[1]; flags=args[2]
        if isinstance(mode,str) and any(c in mode for c in 'wax+'):
            raise PermissionError('verification forbids writes')
        if isinstance(flags,int) and flags & (1|2|64|512|1024):
            raise PermissionError('verification forbids write flags')
    if event.startswith(('socket.','subprocess.','os.exec','os.spawn')) or event in {
        'os.system','os.mkdir','os.remove','os.rmdir','os.rename','os.link','os.symlink',
        'os.chmod','os.chown','os.truncate','os.utime','os.chdir','os.putenv','os.unsetenv',
        'shutil.copyfile','shutil.copymode','shutil.copystat','shutil.rmtree'}:
        raise PermissionError('verification forbids mutation/network/process: '+event)
sys.addaudithook(deny)
runpy.run_path(sys.argv[1],run_name='__main__')
'''

def verify(own,project,anchor):
    before=inventory(own)
    # Snapshot external bytes even on a wrong-anchor/checker failure path.
    r10=project/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r10'
    external_before=inventory(r10)
    context_paths=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json',
      'frontier/campaigns/2026-10-14/elementary-unimodality-parent/fresh-r10-brief.txt',
      'frontier/campaigns/2026-10-14/relative-ci-parent/r10-disposition.json',
      'frontier/campaigns/2026-10-14/relative-ci-parent/r10-verification.json']
    context_before={p:record(project/p) for p in context_paths}
    try:
        counts=authenticate_package(own,anchor)
        baseline=json.loads((own/'input-snapshot-before.json').read_bytes())
        assert baseline['r10_anchor']==R10_ANCHOR
        external=external_inventory(project,baseline)
        r10_counts=authenticate_package(r10,R10_ANCHOR)
        pins=check_pins(project)
        after_input=json.loads((own/'input-snapshot-after.json').read_bytes())
        assert after_input['external_inputs']==baseline, 'before/after external snapshots disagree'
        for e in after_input['new_private_inputs']:
            assert record(own/e['path'])=={k:e[k] for k in ('size','sha256')}
        initial=json.loads((own/'diagnostics-preexecution.json').read_bytes())
        assert record(own/'diagnostics-initial-failed.py.txt')=={k:initial[k] for k in ('size','sha256')}
        final=json.loads((own/'diagnostics-final-preexecution.json').read_bytes())
        assert record(own/'diagnostics.py')=={k:final[k] for k in ('size','sha256')}
        child=subprocess.run([sys.executable,'-I','-B','-c',BOOTSTRAP,str(own/'diagnostics.py')],cwd=own,capture_output=True,timeout=60)
        assert child.returncode==0, 'authenticated checker failed: '+child.stderr.decode(errors='replace')[-1000:]
        assert not child.stderr, 'unexpected checker stderr'
        expected=(own/'diagnostics-receipt.json').read_bytes()
        assert child.stdout==expected,'checker receipt differs'
        return {'status':'PASS_INTEGRITY_AND_EXACT_DIAGNOSTICS_ONLY_C_UNRESOLVED','counted':False,'campaign_accepted':4,
          'seal_sha256':anchor,'own_manifest_counts':counts,'external_r10_manifest_counts':r10_counts,'pinned_blobs':pins,
          'replay_stdout_sha256':hashlib.sha256(child.stdout).hexdigest(),'whole_trees_unchanged':True,
          'independent_mathematical_review':False}
    finally:
        assert inventory(own)==before,'verifier changed own tree'
        assert inventory(r10)==external_before,'verifier changed frozen r10 tree'
        assert {p:record(project/p) for p in context_paths}==context_before,'verifier changed external context'

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--anchor',required=True)
    parser.add_argument('--project-root',type=Path)
    args=parser.parse_args()
    own=Path(__file__).resolve().parent
    project=(args.project_root or own.parents[3]).resolve()
    try:
        result=verify(own,project,args.anchor)
    except Exception as exc:
        print(json.dumps({'status':'REJECTED','error':str(exc),'counted':False}),file=sys.stderr)
        return 1
    print(json.dumps(result,sort_keys=True,indent=2))
    return 0

if __name__=='__main__':
    raise SystemExit(main())
