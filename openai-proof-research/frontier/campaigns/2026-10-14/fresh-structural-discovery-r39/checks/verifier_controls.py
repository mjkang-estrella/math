#!/usr/bin/env python3
"""Exercise strict verifier on disposable local copies; never edit source payload."""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
p=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(p))
from verify import scan
files,dirs=scan(p)
files=[x for x in files if x!='MANIFEST.json']
results=[]
def digest(b):return hashlib.sha256(b).hexdigest()
def manifest(root):
    fs,ds=scan(root);fs=[x for x in fs if x!='MANIFEST.json']
    m={'schema':1,'files':[{'path':n,'bytes':len((root/n).read_bytes()),'sha256':digest((root/n).read_bytes())} for n in fs],'directories':ds}
    raw=(json.dumps(m,indent=2)+'\n').encode();(root/'MANIFEST.json').write_bytes(raw);return digest(raw)
def run(root,anchor,missing=False):
    args=[sys.executable,'-B',str(p/'verify.py'),'--root',str(root)]
    if not missing:args+=['--expected-manifest-sha256',anchor]
    return subprocess.run(args,capture_output=True,text=True)
with tempfile.TemporaryDirectory(prefix='.verify-controls-',dir=p) as d:
    base=Path(d)/'base';base.mkdir()
    for name in dirs:
        if name!='.':(base/name).mkdir(parents=True,exist_ok=True)
    for name in files:shutil.copyfile(p/name,base/name)
    anchor=manifest(base)
    q=run(base,anchor);assert q.returncode==0,q.stderr
    results.append({'name':'positive external anchor','pass':True})
    cases=['wrong anchor','missing anchor','changed payload','missing payload','extra file','extra empty directory','file symlink','directory symlink','hardlinked payload','FIFO','changed manifest']
    for i,name in enumerate(cases):
        root=Path(d)/str(i);shutil.copytree(base,root)
        a=anchor;missing=False
        if name=='wrong anchor':a='0'*64
        elif name=='missing anchor':missing=True
        elif name=='changed payload':(root/'candidate.md').write_bytes((root/'candidate.md').read_bytes()+b'\nchanged\n')
        elif name=='missing payload':(root/'candidate.md').unlink()
        elif name=='extra file':(root/'extra').write_text('extra')
        elif name=='extra empty directory':(root/'extra-empty').mkdir()
        elif name=='file symlink':(root/'linked').symlink_to(root/'candidate.md')
        elif name=='directory symlink':(root/'linked-dir').symlink_to(root/'private',target_is_directory=True)
        elif name=='hardlinked payload':os.link(root/'candidate.md',root/'hardlink')
        elif name=='FIFO':os.mkfifo(root/'fifo')
        elif name=='changed manifest':(root/'MANIFEST.json').write_bytes((root/'MANIFEST.json').read_bytes()+b' ')
        q=run(root,a,missing);assert q.returncode!=0,name
        results.append({'name':name+' rejected','pass':True,'diagnostic':q.stderr.strip().splitlines()[-1]})
        shutil.rmtree(root)
print(json.dumps({'status':'PASS','controls':results,'scope':'Inventory/provenance infrastructure only; no mathematics or contribution gate'},indent=2))
