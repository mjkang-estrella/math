#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Read-only byte authentication before any stored checker or prior replay."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys

PRIOR_SEAL='2084b4bf4268783bb0df3421887d9f7f08079a919cb80715283031d24691337d'


def require(ok,message):
    if not ok:raise RuntimeError(message)


def digest(path):
    data=path.read_bytes()
    return {'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}


def authenticate(root,expected):
    require(len(expected)==64 and all(c in '0123456789abcdef' for c in expected),'invalid external seal')
    require(not (root/'seal.json').is_symlink(),'root seal symlink')
    require(digest(root/'seal.json')['sha256']==expected,'detached root seal mismatch')
    require((root/'seal.sha256').read_text()==expected+'\n','local detached convenience copy mismatch')
    seal=json.loads((root/'seal.json').read_text())
    files={}
    for name,want in seal['inventories'].items():
        require(name in {'input-manifest.json','output-manifest.json'},'invalid inventory name')
        path=root/name
        require(not path.is_symlink(),'inventory symlink')
        require(digest(path)==want,'inventory authentication failed: '+name)
        inventory=json.loads(path.read_text())
        for rel,entry in inventory['files'].items():
            q=Path(rel)
            require(not q.is_absolute() and '..' not in q.parts,'unsafe inventory member')
            require(rel not in files,'duplicate inventory member')
            path=root/q
            require(path.is_file() and not path.is_symlink(),'missing/nonregular member: '+rel)
            require(digest(path)==entry,'content authentication failed: '+rel)
            files[rel]=entry
    require(set(seal['inventories'])=={'input-manifest.json','output-manifest.json'},'incomplete inventories')
    actual=set()
    for path in root.rglob('*'):
        require(not path.is_symlink(),'package symlink prohibited')
        if path.is_file():actual.add(path.relative_to(root).as_posix())
    expected_members=set(files)|set(seal['inventories'])|{'seal.json','seal.sha256'}
    require(actual==expected_members,'inventory membership mismatch: '+str(sorted(actual^expected_members)))
    prior=root/'inputs/private/frozen-r2'
    require(digest(prior/'seal.json')['sha256']==PRIOR_SEAL,'frozen r2 external seal mismatch')
    history=(root/'assignment-and-history.md').read_bytes()
    require((prior/'assignment-and-history.md').read_bytes() in history,'full earlier history not preserved')
    require(history.endswith((prior/'candidate.md').read_bytes()),'full r2 findings not appended verbatim')
    status=json.loads((root/'status.json').read_text())
    require(status['status']=='UNRESOLVED' and status['substantial_complete_result'] is False,'unexpected disposition')
    return len(files)


def replay(root,command,receipt):
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
    p=subprocess.run(command,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)
    require(p.returncode==0,'stored replay failed: '+receipt+' '+p.stderr.decode(errors='replace'))
    require(not p.stderr,'unexpected replay stderr: '+receipt)
    require(p.stdout==(root/receipt).read_bytes(),'stored receipt mismatch: '+receipt)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seal-sha256',help='root of trust from the external handoff; local copy is convenience only')
    ap.add_argument('--authenticate-only',action='store_true')
    args=ap.parse_args();root=Path(__file__).resolve().parent
    expected=args.seal_sha256 or (root/'seal.sha256').read_text().strip()
    count=authenticate(root,expected)
    # Nothing stored is replayed before every inventoried byte and receipt passes.
    if not args.authenticate_only:
        replay(root,[sys.executable,'-B',str(root/'checks.py')],'check-receipt.json')
        replay(root,[sys.executable,'-B',str(root/'inputs/private/frozen-r2/verify.py'),
                     '--seal-sha256',PRIOR_SEAL],'prior-verifier-receipt.json')
    print(json.dumps({'authentication':'PASS','files_authenticated':count,'read_only':True,
        'receipt_replays':'SKIPPED' if args.authenticate_only else 'PASS (own checks and authenticated r2 chain)',
        'seal_sha256':expected,'full_target_B':'UNRESOLVED','U_sharp':'UNPAID',
        'substantial_complete_result':False,'independent_mathematical_review':False},indent=2,sort_keys=True))

if __name__=='__main__':
    try:main()
    except Exception as error:
        print('VERIFICATION FAILED: '+str(error),file=sys.stderr);sys.exit(1)
