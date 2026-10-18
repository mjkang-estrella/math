#!/usr/bin/env python3
# MIT. Reason-checked controls for verify.py. Run only on a disposable copy:
#   controls.py COPY_ROOT EXTERNAL_MANIFEST_SHA256
# All mutations are made in a sibling temporary directory of COPY_ROOT and removed.
import hashlib,json,os,shutil,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
base=Path(sys.argv[1]).absolute();anchor=sys.argv[2]
sys.path.insert(0,str(base))
from verify import verify,inventory

work=Path(tempfile.mkdtemp(prefix='controls-',dir=base.parent))
results=[]
def clone(name):
    d=work/name;shutil.copytree(base,d,symlinks=True)
    shutil.rmtree(d/'__pycache__',ignore_errors=True)
    return d
def reanchor(d):
    (d/'manifest.json').write_text(json.dumps(inventory(d),indent=2,sort_keys=True)+'\n')
    return hashlib.sha256((d/'manifest.json').read_bytes()).hexdigest()
def expect(name,root,a,text):
    try:verify(root,a)
    except ValueError as e:
        if text not in str(e):raise SystemExit('WRONG REASON '+name+': '+str(e))
        results.append({'case':name,'rejected':True,'message':str(e)})
    else:raise SystemExit('ACCEPTED mutation '+name)

INV='exact directory/file inventory mismatch'
try:
    n=verify(clone('positive'),anchor);results.append({'case':'positive','accepted':True,'counts':list(n)})
    expect('zero-anchor',clone('zero-anchor'),'0'*64,'external anchor mismatch')
    expect('short-anchor',clone('short-anchor'),anchor[:-1],'external anchor mismatch')
    d=clone('changed-verdict');p=d/'review.md';p.write_bytes(p.read_bytes().replace(b'CONTRIBUTION: TECHNICAL',b'CONTRIBUTION: SUBSTANTIAL',1))
    expect('changed-verdict',d,anchor,INV)
    d=clone('missing-file');(d/'reading-limits.md').unlink();expect('missing-file',d,anchor,INV)
    d=clone('extra-file');(d/'extra').write_text('m');expect('extra-file',d,anchor,INV)
    d=clone('extra-empty-directory');(d/'extra-empty').mkdir();expect('extra-empty-directory',d,anchor,INV)
    d=clone('payload-symlink');p=d/'review.md';p.unlink();p.symlink_to(base/'review.md')
    expect('payload-symlink',d,anchor,'link/nonregular: review.md')
    d=clone('directory-symlink');shutil.rmtree(d/'private');(d/'private').symlink_to(base/'private',target_is_directory=True)
    expect('directory-symlink',d,anchor,'link/nonregular: private')
    d=clone('root-symlink');link=work/'root-link';link.symlink_to(d,target_is_directory=True)
    expect('root-symlink',link,anchor,'root/ancestor link or non-directory')
    d=clone('ancestor-symlink');link=work/'anc-link';link.symlink_to(work,target_is_directory=True)
    expect('ancestor-symlink',link/d.name,anchor,'root/ancestor link or non-directory')
    d=clone('hardlinked-payload');os.link(d/'review.md',work/'hl-payload')
    expect('hardlinked-payload',d,anchor,'hardlink: review.md')
    d=clone('fifo-payload');p=d/'review.md';p.unlink();os.mkfifo(p)
    expect('fifo-payload',d,anchor,'link/nonregular: review.md')
    d=clone('hardlinked-manifest');os.link(d/'manifest.json',work/'hl-manifest')
    expect('hardlinked-manifest',d,anchor,'manifest link/nonregular')
    d=clone('changed-manifest');(d/'manifest.json').write_text('{}\n')
    expect('changed-manifest',d,anchor,'external anchor mismatch')
    # Re-anchored counterfeits: self-consistent inventory, content checks must still reject.
    d=clone('reanchored-primary-pdf');p=d/'private/deprez-vaes-jncg2011.pdf';p.write_bytes(p.read_bytes()+b'\n')
    expect('reanchored-primary-pdf',d,reanchor(d),'primary receipt mismatch: private/deprez-vaes-jncg2011.pdf')
    d=clone('reanchored-primary-text');p=d/'private/arano-vaes-1602.03047.txt';p.write_bytes(p.read_bytes()+b'\n')
    expect('reanchored-primary-text',d,reanchor(d),'primary receipt mismatch: private/arano-vaes-1602.03047.txt')
    d=clone('reanchored-author-anchor');p=d/'author-controls-result.json'
    p.write_bytes(p.read_bytes().replace(b'4d14a7c7',b'4d14a7c8',1))
    expect('reanchored-author-anchor',d,reanchor(d),'author packet anchor mismatch')
finally:
    shutil.rmtree(work)
print(json.dumps({'integrity_only':True,'all_reasons_ok':True,'results':results},indent=1))
