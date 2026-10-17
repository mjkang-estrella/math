#!/usr/bin/env python3
"""Read-only, externally anchored screen inventory verification. MIT."""
import argparse,hashlib,json,pathlib,subprocess,sys

def sha(b):return hashlib.sha256(b).hexdigest()
def main():
    a=argparse.ArgumentParser();a.add_argument('--anchor',required=True);args=a.parse_args()
    root=pathlib.Path(__file__).resolve().parent
    raw=(root/'output-manifest.json').read_bytes()
    assert sha(raw)==args.anchor,'wrong external anchor'
    m=json.loads(raw); files={}; dirs=[]
    for p in root.rglob('*'):
        assert not p.is_symlink(),'symlink forbidden'
        rel=p.relative_to(root).as_posix()
        if p.is_dir():dirs.append(rel)
        elif p.is_file() and rel!='output-manifest.json':files[rel]=p
        elif not p.is_file():raise AssertionError('nonregular payload')
    assert set(files)==set(m['files']),'file membership mismatch'
    assert sorted(dirs)==m['directories'],'directory membership mismatch'
    for rel,p in files.items():
        b=p.read_bytes();r=m['files'][rel]
        assert sha(b)==r['sha256'] and len(b)==r['bytes'],f'changed payload {rel}'
    contexts=json.loads((root/'context-receipt.json').read_text())
    for r in contexts:
        b=(root/r['snapshot']).read_bytes()
        assert sha(b)==r['sha256'] and len(b)==r['bytes']
    tr=next(r for r in contexts if r['original']=='sources/preprints-tree.json')
    tree=json.loads((root/tr['snapshot']).read_text())
    assert tree['truncated'] is False
    blobs={r['path']:r['sha'] for r in tree['tree'] if r['type']=='blob'}
    count=0
    for receipt in ['source-receipt.json','source065-receipt.json']:
        for r in json.loads((root/receipt).read_text()):
            b=(root/r['local']).read_bytes()
            assert sha(b)==r['sha256'] and len(b)==r['bytes']
            assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']==blobs[r['path']]
            assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+r['path'] in r['url']
            count+=1
    assert count==47
    prim=json.loads((root/'primary-receipt.json').read_text())+[json.loads((root/'primary065-receipt.json').read_text())]
    for r in prim:assert sha((root/r['local']).read_bytes())==r['sha256']
    actual=subprocess.run([sys.executable,str(root/'check_129.py')],capture_output=True,text=True,check=True)
    assert json.loads(actual.stdout)==json.loads((root/'finite-checks.json').read_text()),'finite check mismatch'
    print(json.dumps({'status':'INTEGRITY_AND_FINITE_CHECKS_PASS','payloads':len(files),'directories':len(dirs),'pinned_blobs':count,'primary_receipts':len(prim),'scope':'No mathematical or contribution verdict.'},sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
