"""MIT. Read-only detached-anchor inventory/provenance verifier. No math gates."""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path, PurePosixPath

def sha(b): return hashlib.sha256(b).hexdigest()
def unique(pairs):
    d={}
    for k,v in pairs:
        if k in d: raise ValueError('duplicate JSON key: '+k)
        d[k]=v
    return d

def read_json(p): return json.loads(p.read_bytes(),object_pairs_hook=unique)
def require(c,msg):
    if not c: raise ValueError(msg)
def audit(event,args):
    if event=='open':
        mode=args[1]; flags=args[2]
        if (isinstance(mode,str) and any(x in mode for x in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise PermissionError('read-only verifier')
    if event.startswith(('socket.','subprocess.')) or event in {'os.remove','os.rename','os.rmdir','os.mkdir','os.link','os.symlink','os.chmod','os.system','os.truncate','os.utime','os.chown'}:
        raise PermissionError('read-only verifier')

def validpath(s):
    require(isinstance(s,str) and s!='' and '\\' not in s,'bad inventory path')
    p=PurePosixPath(s)
    require(not p.is_absolute() and all(q not in {'','..','.'} for q in p.parts) and str(p)==s,'unsafe inventory path')

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--packet',required=True)
p.add_argument('--finalhash',required=True,help='detached SHA256 of MANIFEST.json')
p.add_argument('--reporthash',required=True,help='detached SHA256 of public/report.md')
p.add_argument('--tree',required=True,help='complete canonical sources/preprints-tree.json')
a=p.parse_args()
sys.addaudithook(audit)
try:
    require(re.fullmatch('[0-9a-f]{64}',a.finalhash) is not None,'malformed finalhash')
    require(re.fullmatch('[0-9a-f]{64}',a.reporthash) is not None,'malformed reporthash')
    root=Path(a.packet).absolute()
    require(not root.is_symlink() and root.is_dir(),'packet root must be a real directory')
    mf=root/'MANIFEST.json'
    require(mf.is_file() and not mf.is_symlink() and mf.stat().st_nlink==1,'manifest type/link count')
    require(sha(mf.read_bytes())==a.finalhash,'DETACHED manifest hash mismatch')
    m=read_json(mf)
    require(m['schema']=='r118-exact-packet-v1','manifest schema')
    require(m['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','pin mismatch')
    require(m['report']=={'path':'public/report.md','sha256':a.reporthash},'DETACHED report hash mismatch')
    expected={}
    for row in m['files']:
        rel=row['path']; validpath(rel)
        require(rel not in expected and rel!='MANIFEST.json','duplicate/self inventory')
        require(re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None,'bad file hash')
        expected[rel]=row
    dirs=m['directories']
    require(len(set(dirs))==len(dirs),'duplicate directory')
    for rel in dirs: validpath(rel)
    found={}; founddirs=[]
    for base,subdirs,files in os.walk(root,followlinks=False):
        for name in subdirs:
            path=Path(base)/name; rel=path.relative_to(root).as_posix()
            require(not path.is_symlink(),'symlink directory '+rel)
            require(stat.S_ISDIR(path.lstat().st_mode),'not directory '+rel)
            founddirs.append(rel)
        for name in files:
            path=Path(base)/name; rel=path.relative_to(root).as_posix(); s=path.lstat()
            require(stat.S_ISREG(s.st_mode) and not path.is_symlink() and s.st_nlink==1,'nonregular/link file '+rel)
            if rel=='MANIFEST.json': continue
            found[rel]={'path':rel,'bytes':s.st_size,'mode':stat.S_IMODE(s.st_mode),'sha256':sha(path.read_bytes())}
    require(set(found)==set(expected),'exact file inventory mismatch')
    require(set(founddirs)==set(dirs),'exact directory inventory mismatch')
    for rel,row in expected.items(): require(found[rel]==row,'file identity mismatch '+rel)
    require(sha((root/'public/report.md').read_bytes())==a.reporthash,'report bytes mismatch')
    receipt=read_json(root/'private/tree-receipt.json')
    tb=Path(a.tree).read_bytes()
    require(sha(tb)==receipt['sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','complete-tree SHA256 mismatch')
    tree=json.loads(tb,object_pairs_hook=unique)
    require(tree['truncated'] is False and len(tree['tree'])==13223,'incomplete canonical tree')
    index={r['path']:r for r in tree['tree']}
    require(len(index)==13223,'duplicate tree paths')
    require(sum(r['type']=='blob' for r in index.values())==10373,'canonical blob count')
    sources=read_json(root/'private/upstream-receipts.json')
    require(len(sources)==31,'source count')
    for row in sources:
        validpath(row['local']); b=(root/row['local']).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(blob==row['git_blob']==index[row['path']]['sha'],'canonical Git blob mismatch')
        require(sha(b)==row['sha256'] and len(b)==row['bytes'],'source SHA/size mismatch')
        require(row['url']=='https://raw.githubusercontent.com/openai/math/'+m['pin']+'/'+row['path'],'raw pinned URL mismatch')
    selected={r['path']:r for r in receipt['selected']}
    require(set(selected)=={r['path'] for r in sources},'canonical selection mismatch')
    for path,row in selected.items(): require(row==index[path],'selected full-tree record mismatch')
    public=read_json(root/'public/source-register.json')
    require(public['pin']==m['pin'] and len(public['sources'])==len(sources),'public source register mismatch')
    for pub,priv in zip(public['sources'],sources):
        require({k:v for k,v in pub.items() if k!='labels_navigation_only'}==priv,'public/private source binding')
    prim=read_json(root/'private/primary-receipts.json')
    require(prim==read_json(root/'public/primary-register.json'),'primary register mismatch')
    for row in prim:
        for ext,key in [('pdf','pdf_sha256'),('txt','text_sha256')]:
            require(sha((root/('private/primary/'+row['name']+'.'+ext)).read_bytes())==row[key],'primary bytes mismatch')
    print(json.dumps({'integrity':'verified','files':len(found),'directories':len(founddirs),'canonical_upstream_blobs':len(sources),'primary_pairs':len(prim),'finalhash':a.finalhash,'reporthash':a.reporthash,'mathematical_gate':False},sort_keys=True))
except (ValueError,KeyError,TypeError,OSError) as e:
    print('REJECT: '+str(e),file=sys.stderr); sys.exit(1)
