#!/usr/bin/env python3
"""Optional destructive-copy integrity controls; original code MIT.
Writes only temporary copies inside this round's owned directory, removes them,
and emits a receipt to stdout. Never imports or executes historical code.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys

META={'seal.json','seal.sha256','inputs-manifest.json','outputs-manifest.json'}
def rec(p):
    b=p.read_bytes();return {'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def inv(p):
    return {str(q.relative_to(p)):rec(q) for q in sorted(p.rglob('*')) if q.is_file()}
def encode(d):
    return (json.dumps(d,sort_keys=True,indent=2)+'\n').encode()
def reseal(p):
    seal=json.loads((p/'seal.json').read_bytes())
    for mn in ('inputs-manifest.json','outputs-manifest.json'):
        data=json.loads((p/mn).read_bytes())
        for e in data['files']:
            e.update(rec(p/e['path']))
        (p/mn).write_bytes(encode(data));seal['manifests'][mn]={'path':mn,**rec(p/mn)}
    (p/'seal.json').write_bytes(encode(seal));anchor=rec(p/'seal.json')['sha256']
    (p/'seal.sha256').write_text(anchor+'\n');return anchor

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);args=ap.parse_args()
    own=Path(__file__).resolve().parent;project=own.parents[3]
    before=inv(own);assert rec(own/'seal.json')['sha256']==args.anchor
    trusted=set(META); trusted_verifier=None
    seal=json.loads((own/'seal.json').read_bytes())
    for mn in ('inputs-manifest.json','outputs-manifest.json'):
        assert rec(own/mn)=={k:seal['manifests'][mn][k] for k in ('size','sha256')}
        for e in json.loads((own/mn).read_bytes())['files']:
            assert rec(own/e['path'])=={k:e[k] for k in ('size','sha256')}
            trusted.add(e['path'])
            if e['path']=='verify.py':trusted_verifier=rec(own/'verify.py')
    assert set(before)==trusted
    historical=project/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r10'
    h_before=inv(historical)
    temp=own/'.integrity-controls';assert not temp.exists();temp.mkdir()
    results={}
    try:
        def copied(name):
            dst=temp/name;dst.mkdir()
            for rel in sorted(trusted):
                p=dst/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((own/rel).read_bytes())
            return dst
        def run(dst,anchor):
            assert rec(dst/'verify.py')==trusted_verifier
            b=inv(dst)
            r=subprocess.run([sys.executable,'-I','-B',str(dst/'verify.py'),'--anchor',anchor,'--project-root',str(project)],capture_output=True,timeout=60)
            assert inv(dst)==b and inv(historical)==h_before
            return r
        good=copied('good');r=run(good,args.anchor)
        assert r.returncode==0,r.stderr.decode();results['baseline_replay']=json.loads(r.stdout)['status']
        r=run(good,'0'*64);assert r.returncode!=0 and b'external anchor mismatch' in r.stderr
        results['wrong_anchor_rejected']=True
        corrupt=copied('corrupt');(corrupt/'candidate.md').write_bytes((corrupt/'candidate.md').read_bytes()+b'\ncorrupted\n')
        r=run(corrupt,args.anchor);assert r.returncode!=0 and b'payload authentication' in r.stderr
        results['payload_corruption_rejected']=True
        for name,suffix,needle in [('checker_failure',b'\nraise RuntimeError("injected authenticated checker failure")\n',b'authenticated checker failed'),('write_attempt',b'\nopen("forbidden-write-control", "w").write("must not exist")\n',b'verification forbids writes')]:
            dst=copied(name);p=dst/'diagnostics.py';p.write_bytes(p.read_bytes()+suffix)
            pre=dst/'diagnostics-final-preexecution.json';d=json.loads(pre.read_bytes());d.update(rec(p));pre.write_bytes(encode(d))
            anchor=reseal(dst);r=run(dst,anchor)
            assert r.returncode!=0 and needle in r.stderr,r.stderr.decode()
            assert not (dst/'forbidden-write-control').exists()
            results['authenticated_'+name+'_rejected']=True
            results[name+'_error']=json.loads(r.stderr)['error'][-300:]
    finally:
        shutil.rmtree(temp)
        assert inv(own)==before,'original package changed in controls'
        assert inv(historical)==h_before,'historical tree changed in controls'
    print(json.dumps({'status':'PASS_INTEGRITY_REJECTION_CONTROLS_ONLY','tested_provisional_anchor':args.anchor,'original_and_copied_trees_unchanged':True,'temporary_copies_removed':True,'controls':results,'counted':False},sort_keys=True,indent=2))
if __name__=='__main__':
    main()
