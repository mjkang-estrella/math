#!/usr/bin/env python3
"""Read-only external-anchor integrity verifier; not mathematical review."""
import argparse,hashlib,json,pathlib,sys

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,reason):
    if not ok:raise ValueError(reason)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--repo',type=pathlib.Path);ap.add_argument('--private',action='store_true');a=ap.parse_args()
    b=pathlib.Path(__file__).resolve().parent;m=b/'MANIFEST.json'
    require(digest(m)==a.manifest_sha256,'external manifest anchor mismatch')
    j=json.loads(m.read_text());require(j['accepted'] is False and j['count_change']==0,'invalid acceptance status')
    require(j['review_gates']=='PENDING','invalid review status')
    expected={r['path'] for r in j['files']};actual={p.relative_to(b).as_posix() for p in b.rglob('*') if p.is_file() and 'private' not in p.relative_to(b).parts and '__pycache__' not in p.relative_to(b).parts and p.name!='MANIFEST.json'}
    require(expected==actual,'public membership mismatch')
    for r in j['files']:
        p=b/r['path'];require(not p.is_symlink() and p.stat().st_nlink==1,'unsafe payload link');require(digest(p)==r['sha256'],'payload hash mismatch: '+r['path'])
    scope=json.loads((b/'scope-status.json').read_text());require(scope['target']==j['target'],'scope mismatch');require(scope['accepted'] is False and scope['count_change']==0,'scope status mismatch')
    if a.repo:
        tree={e['path']:e.get('sha') for e in json.loads((a.repo/'sources/preprints-tree.json').read_text())['tree'] if e['type']=='blob'}
        for r in json.loads((b/'source-receipts.json').read_text()):
            require(tree.get(r['path'])==r['blob'],'canonical source membership mismatch')
            require('/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in r['url'],'wrong source pin')
    if a.private:
        for r in json.loads((b/'source-receipts.json').read_text()):
            p=b/'private'/'/'.join(r['path'].split('/')[2:]);d=p.read_bytes();require(digest(p)==r['sha256'],'private source hash mismatch');require(hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==r['blob'],'private source blob mismatch')
        for r in json.loads((b/'primary-receipts.json').read_text()):
            require(digest(b/r['private_pdf'])==r['sha256'],'primary PDF hash mismatch');require(digest(b/r['private_text'])==r['text_sha256'],'primary text hash mismatch')
    print(json.dumps({'status':'PASS_IDENTITY_ONLY','public_files':len(expected),'full_theorem_verified':False}))
if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,OSError) as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
