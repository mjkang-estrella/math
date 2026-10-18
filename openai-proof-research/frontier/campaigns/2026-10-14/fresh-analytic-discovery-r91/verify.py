#!/usr/bin/env python3
"""Read-only identity and open-status verifier, not a mathematical review."""
import argparse,hashlib,json,pathlib,sys

def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def req(v,s):
    if not v:raise ValueError(s)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--repo',type=pathlib.Path);ap.add_argument('--private',action='store_true');a=ap.parse_args();b=pathlib.Path(__file__).resolve().parent
    req(h(b/'MANIFEST.json')==a.manifest_sha256,'external anchor mismatch');m=json.loads((b/'MANIFEST.json').read_text())
    req(m['status']=='UNRESOLVED_FULL_TARGET_NO_NOMINEE','invalid outcome');req(m['accepted'] is False and m['published'] is False and m['count_change']==0,'invalid campaign status')
    actual={p.relative_to(b).as_posix() for p in b.rglob('*') if p.is_file() and 'private' not in p.relative_to(b).parts and p.name!='MANIFEST.json'};expected={r['path'] for r in m['files']};req(actual==expected,'public membership mismatch')
    for r in m['files']:
        rel=pathlib.PurePosixPath(r['path']);req(not rel.is_absolute() and '..' not in rel.parts,'unsafe path');p=b/rel;req(not p.is_symlink() and p.stat().st_nlink==1,'unsafe payload link');req(h(p)==r['sha256'],'payload hash mismatch: '+r['path'])
    s=json.loads((b/'scope-status.json').read_text());req(s['target']==m['target'],'scope mismatch');req(s['status']=='PROSPECTIVE_FULL_TARGET_OPEN','scope status mismatch')
    c=json.loads((b/'checkpoint.json').read_text());req(c['full_target_proved'] is False and c['nominee'] is False,'checkpoint status mismatch')
    rows=json.loads((b/'source-receipts.json').read_text())
    if a.repo:
        tree={r['path']:r['sha'] for r in json.loads((a.repo/'sources/preprints-tree.json').read_text())['tree'] if r['type']=='blob'}
        for r in rows:req(tree.get(r['path'])==r['blob'],'canonical source mismatch');req('/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in r['url'],'wrong source pin')
    if a.private:
        for r in rows:
            p=b/'private'/'/'.join(r['path'].split('/')[2:]);d=p.read_bytes();req(h(p)==r['sha256'],'private source hash mismatch');req(hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==r['blob'],'private source blob mismatch')
        for r in json.loads((b/'primary-receipts.json').read_text()):req(h(b/r['private_pdf'])==r['pdf_sha256'] and h(b/r['private_text'])==r['text_sha256'],'primary identity mismatch')
    print(json.dumps({'status':'PASS_IDENTITY_ONLY','public_files':len(expected),'full_target_proved':False,'nominee':False}))
if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,OSError) as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
