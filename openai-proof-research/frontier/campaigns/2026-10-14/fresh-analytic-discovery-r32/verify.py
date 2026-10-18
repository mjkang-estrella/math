#!/usr/bin/env python3
# Original code by Myeongjin Kang; MIT. Byte integrity, not mathematical validation.
import argparse,hashlib,json,os,stat,subprocess,sys
from pathlib import Path,PurePosixPath

def require(ok,msg):
    if not ok:raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def safe_rel(s):
    p=PurePosixPath(s)
    require(isinstance(s,str) and str(p)==s and not p.is_absolute() and '..' not in p.parts and s not in ('','.'),'unsafe path')
    return p

def inventory(root):
    files={};dirs=[]
    for base,ds,fs in os.walk(root,followlinks=False):
        for n in ds+fs:
            p=Path(base)/n; st=p.lstat(); rel=p.relative_to(root).as_posix()
            require(not stat.S_ISLNK(st.st_mode),'symlink: '+rel)
            if stat.S_ISDIR(st.st_mode):dirs.append(rel)
            else:
                require(stat.S_ISREG(st.st_mode),'nonregular: '+rel)
                require(st.st_nlink==1,'hardlink: '+rel)
                if rel!='manifest.json':files[rel]={'bytes':st.st_size,'sha256':digest(p.read_bytes())}
    return files,sorted(dirs)

def main():
    a=argparse.ArgumentParser();a.add_argument('--anchor',required=True);a.add_argument('--root',default=str(Path(__file__).absolute().parent));ns=a.parse_args()
    require(len(ns.anchor)==64 and all(c in '0123456789abcdef' for c in ns.anchor),'anchor must be lowercase SHA256')
    root=Path(ns.root).absolute()
    for p in [root]+list(root.parents):require(not p.is_symlink(),'symlink root/ancestor')
    require(root.is_dir(),'missing root')
    mp=root/'manifest.json';require(mp.is_file() and not mp.is_symlink() and mp.stat().st_nlink==1,'unsafe manifest')
    raw=mp.read_bytes();require(digest(raw)==ns.anchor,'external anchor mismatch')
    m=json.loads(raw);require(m['schema']=='r32-exact-inventory-v1','schema')
    for s in m['files']:safe_rel(s);require(s!='manifest.json','self entry')
    for s in m['directories']:safe_rel(s)
    files,dirs=inventory(root);require(files==m['files'],'exact file inventory/hash mismatch');require(dirs==m['directories'],'exact directory inventory mismatch')
    tree=json.loads((root/'private/context/preprints-tree.json').read_text());require(tree.get('truncated') is False,'truncated source tree')
    require(len(tree['tree'])==13223,'unexpected tree length');blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
    pin=json.loads((root/'private/context/upstream.json').read_text())['commit'];require(pin=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','pin mismatch')
    checked=0
    for receipt in ('source-receipts.json','263-source-receipts.json'):
        for x in json.loads((root/receipt).read_text()):
            safe_rel(x['local']);b=(root/x['local']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            require(blob==x['git_blob']==blobs[x['path']],'source blob mismatch')
            require(digest(b)==x['sha256'],'source SHA mismatch')
            require(x['url']=='https://raw.githubusercontent.com/openai/math/'+pin+'/'+x['path'],'unpinned source URL');checked+=1
    x=json.loads((root/'263-lean-doc-receipt.json').read_text());safe_rel(x['local_path']);b=(root/x['local_path']).read_bytes()
    require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['api_git_blob']==x['actual_git_blob'],'Lean doc blob mismatch')
    require(digest(b)==x['sha256'] and len(b)==x['bytes'],'Lean doc hash mismatch')
    pdfs=0
    for x in json.loads((root/'primary-receipts.json').read_text()):
        safe_rel(x['local']);p=root/x['local'];require(digest(p.read_bytes())==x['sha256'],'primary PDF hash mismatch')
        out=subprocess.run(['pdftotext','-layout',str(p),'-'],check=True,capture_output=True).stdout
        require(out==p.with_suffix('.txt').read_bytes(),'primary text extraction differs');pdfs+=1
    scope=json.loads((root/'263-scope-freeze.json').read_text())
    require(digest((root/'263-scope.md').read_bytes())==scope['scope_sha256'],'scope changed')
    require(digest((root/'263-working-proof.md').read_bytes())==scope['working_proof_sha256'],'proof changed since scope record')
    out=subprocess.run([sys.executable,str(root/'exponent_checks.py')],check=True,capture_output=True,text=True).stdout
    require(json.loads(out)==json.loads((root/'exponent-checks.json').read_text()),'arithmetic replay changed')
    print(json.dumps({'status':'PASS_INTEGRITY_ONLY','payload_files':len(files),'directories':len(dirs),'pinned_preprint_blobs':checked,'additional_pinned_doc_blobs':1,'primary_pdf_bindings':pdfs,'scope_unchanged':True,'arithmetic_replay':'PASS_NONPROOF','limits':'No proof, substantiality, formalization, or acceptance verdict.'},indent=2))
if __name__=='__main__':
    try:main()
    except Exception as e:
        print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
