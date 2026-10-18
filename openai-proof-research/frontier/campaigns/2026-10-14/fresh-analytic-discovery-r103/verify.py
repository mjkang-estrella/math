#!/usr/bin/env python3
"""Packet identities and finite support only; never an independent theorem gate."""
import argparse, hashlib, json
from pathlib import Path

PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
SCOPE='ab52a8e5ed90a18ca5871b6d74ed8b88e1439803ef6e3fd23ccb553c0c7ef2e4'
def sha(b):return hashlib.sha256(b).hexdigest()
def require(ok,reason):
    if not ok:raise ValueError(reason)
def verify(root,anchor,tree=None,private=False):
    raw=(root/'MANIFEST.json').read_bytes()
    require(sha(raw)==anchor,'external manifest anchor mismatch')
    m=json.loads(raw); files=m['files']
    require(m['source_pin']==PIN,'source pin mismatch')
    require(m['independent_gates']=={'proof':'pending','contribution':'pending'},'independent gates must remain pending')
    require(m['accepted'] is False and m['published'] is False and m['count_change']==0,'acceptance/publication/count forbidden')
    actual={str(x.relative_to(root)) for x in root.rglob('*') if x.is_file() and 'private' not in x.relative_to(root).parts and x.name!='MANIFEST.json'}
    require(actual==set(files),'public inventory mismatch')
    for name,h in files.items():
        require(not Path(name).is_absolute() and '..' not in Path(name).parts and 'private' not in Path(name).parts,'unsafe payload path')
        require(sha((root/name).read_bytes())==h,'payload hash mismatch: '+name)
    require(sha((root/'scope-status.json').read_bytes())==SCOPE,'frozen scope anchor mismatch')
    st=json.loads((root/'author-assembly-status.json').read_text())
    require(st['scope_sha256']==SCOPE,'status scope anchor mismatch')
    require(st['independent_proof_gate']=='pending' and st['independent_contribution_gate']=='pending','status gates must remain pending')
    require(st['accepted'] is False and st['published'] is False and st['count_change']==0,'status acceptance forbidden')
    for name,h in st['modules'].items():require(files[name]==h,'module anchor mismatch')
    canonical=None
    if tree:
        t=json.loads(Path(tree).read_text());require(t.get('truncated',False) is False,'truncated canonical tree forbidden')
        canonical={x['path']:x['sha'] for x in t['tree'] if x['type']=='blob'}
    count=0
    for receipt in ('source220-receipts.json','source224-receipts.json'):
        for r in json.loads((root/receipt).read_text()):
            require(r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path'],'receipt URL/pin mismatch')
            if canonical is not None:require(canonical.get(r['path'])==r['git_blob'],'canonical source membership mismatch')
            if private:
                b=(root/'private'/r['path']).read_bytes()
                require(sha(b)==r['sha256'],'private source SHA mismatch')
                require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob'],'private Git blob mismatch')
            count+=1
    if private:
        for r in json.loads((root/'primary-receipts.json').read_text()):
            require(sha((root/'private/primaries'/(r['name']+'.pdf')).read_bytes())==r['sha256'],'primary PDF mismatch')
    return {'status':'PASS_PACKET_IDENTITIES_ONLY','public_payloads':len(files),'source_receipts':count,
            'canonical_membership_checked':canonical is not None,'private_bytes_checked':private,
            'independent_proof':'pending','independent_contribution':'pending','full_theorem_computationally_verified':False}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--manifest-sha256',required=True);p.add_argument('--canonical-tree');p.add_argument('--private',action='store_true');a=p.parse_args()
    try:print(json.dumps(verify(a.root,a.manifest_sha256,a.canonical_tree,a.private),indent=2,sort_keys=True))
    except (ValueError,KeyError,OSError) as e:raise SystemExit('REJECT: '+str(e))
