#!/usr/bin/env python3
"""Read-only public integrity verifier; optional private-cache authentication."""
import argparse,hashlib,json,stat
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);p.add_argument('--tree',type=Path,required=True);p.add_argument('--cache-root',type=Path);a=p.parse_args();r=Path(__file__).absolute().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def need(c,s):
    if not c:raise SystemExit(s)
def public():
    for x in r.iterdir():
        if x.name=='private':
            need(x.is_dir() and not x.is_symlink(),'PRIVATE_BOUNDARY');continue
        yield x
        if x.is_dir():yield from x.rglob('*')
xs=list(public())
for x in xs:
    st=x.lstat();need(not stat.S_ISLNK(st.st_mode),'SYMLINK');need(stat.S_ISREG(st.st_mode) or stat.S_ISDIR(st.st_mode),'NONREGULAR')
    if x.is_file():need(st.st_nlink==1,'HARDLINK')
m=r/'MANIFEST.json';need(H(m.read_bytes())==a.anchor,'MANIFEST_ANCHOR');d=json.loads(m.read_text());need(set(d)=={str(x.relative_to(r)) for x in xs if x.is_file() and x!=m},'EXACT_MEMBERSHIP')
expected={'.'}
for name,v in d.items():
    q=Path(name);need(not q.is_absolute() and '..' not in q.parts and q.parts[0]!='private','UNSAFE_MEMBER');expected.update(str(z) for z in q.parents)
    b=(r/q).read_bytes();need(H(b)==v['sha256'] and len(b)==v['bytes'],'PAYLOAD_HASH:'+name)
need(expected=={'.'}|{str(x.relative_to(r)) for x in xs if x.is_dir()},'DIRECTORY_MEMBERSHIP')
tb=a.tree.read_bytes();need(H(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','TREE_ANCHOR');t=json.loads(tb);need(len(t['tree'])==13223 and t.get('truncated') is False,'TREE_COMPLETE');es={x['path']:x for x in t['tree']}
n=0
for f,count in [('source-receipts.json',3)]:
    s=json.loads((r/f).read_text());need(s['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' and s['tree_sha256']==H(tb) and s['entries']==13223,'SOURCE_PIN')
    selected={x['path'] for x in t['tree'] if x['type']=='blob' and x['path'].split('/')[1] in s['selected_folders'] and not x['path'].endswith('.pdf')}
    need(len(s['files'])==len(selected)==count and {x['source_path'] for x in s['files']}==selected,'CANONICAL_SELECTION')
    for x in s['files']:
        need(x['git_blob']==es[x['source_path']]['sha'] and x['bytes']==es[x['source_path']]['size'],'CANONICAL_RECEIPT')
        need(x['url']=='https://raw.githubusercontent.com/openai/math/'+s['pin']+'/'+x['source_path'],'SOURCE_URL')
        if a.cache_root:
            b=(a.cache_root/x['path']).read_bytes();g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();need(g==x['git_blob'] and H(b)==x['sha256'] and len(b)==x['bytes'],'CANONICAL_BYTES')
        n+=1
if a.cache_root:
    for x in json.loads((r/'primary-identities.json').read_text())['files']:
        b=(a.cache_root/x['path']).read_bytes();need(H(b)==x['sha256'] and len(b)==x['bytes'],'PRIMARY_BYTES')
print(json.dumps({'status':'PASS','public_payloads':len(d),'canonical_receipts':n,'private_bytes_checked':bool(a.cache_root),'limits':'Integrity only; exploratory checkpoint, no frozen target, no nominee, no mathematical review.'}))
