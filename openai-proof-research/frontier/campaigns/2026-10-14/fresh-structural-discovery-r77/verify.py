#!/usr/bin/env python3
"""Packet integrity and canonical identities; not mathematical verification."""
import argparse,hashlib,json,stat
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);ap.add_argument('--tree',type=Path,required=True);a=ap.parse_args();r=Path(__file__).absolute().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def need(ok,why):
    if not ok:raise SystemExit(why)
for x in [r,*r.rglob('*')]:
    st=x.lstat();need(not stat.S_ISLNK(st.st_mode),'SYMLINK')
    need(stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode),'NONREGULAR')
    if stat.S_ISREG(st.st_mode):need(st.st_nlink==1,'HARDLINK')
m=r/'MANIFEST.json';need(H(m.read_bytes())==a.anchor,'MANIFEST_ANCHOR');d=json.loads(m.read_text())
need(set(d)=={str(x.relative_to(r)) for x in r.rglob('*') if x.is_file() and x!=m},'EXACT_MEMBERSHIP')
expected_dirs={'.'}
for name,v in d.items():
    q=Path(name);need(not q.is_absolute() and '..' not in q.parts,'UNSAFE_MEMBER')
    expected_dirs.update(str(z) for z in q.parents)
    b=(r/q).read_bytes();need(H(b)==v['sha256'] and len(b)==v['bytes'],'PAYLOAD_HASH:'+name)
need(expected_dirs=={'.'}|{str(x.relative_to(r)) for x in r.rglob('*') if x.is_dir()},'DIRECTORY_MEMBERSHIP')
need(H((r/'scope-freeze.md').read_bytes())=='66056cf6b75951e864e69b51386d9729389f3b96f67e62b6cf5064eff9101a5b','SCOPE_ANCHOR')
tb=a.tree.read_bytes();need(H(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','TREE_ANCHOR');t=json.loads(tb);need(len(t['tree'])==13223 and t.get('truncated') is False,'TREE_COMPLETE');es={v['path']:v for v in t['tree']}
s=json.loads((r/'source-receipts.json').read_text());need(s['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','SOURCE_PIN');need(s['tree_sha256']==H(tb),'RECEIPT_TREE')
selected={e['path'] for e in t['tree'] if e['type']=='blob' and 'Relative-generation-and-the-generator-problem-for-finite-factors-' in e['path'] and not e['path'].endswith('.pdf')}
need(len(s['files'])==len(selected)==9 and {v['source_path'] for v in s['files']}==selected,'CANONICAL_SELECTION')
for v in s['files']:
    b=(r/v['path']).read_bytes();g=hashlib.sha1(b'blob '+str(len(b)).encode()+bytes([0])+b).hexdigest()
    need(g==v['git_blob']==es[v['source_path']]['sha'] and H(b)==v['sha256'] and len(b)==v['bytes'],'CANONICAL_BLOB:'+v['source_path'])
    need(v['url']=='https://raw.githubusercontent.com/openai/math/'+s['pin']+'/'+v['source_path'],'SOURCE_URL')
for v in json.loads((r/'primary-receipts.json').read_text()):
    need(H((r/v['file']).read_bytes())==v['sha256'] and H((r/v['text_file']).read_bytes())==v['text_sha256'],'PRIMARY_RECEIPT')
print(json.dumps(dict(status='PASS',payloads=len(d),canonical_blobs=9,tree_entries=13223,scope='unchanged',limits='Integrity only; not a theorem or contribution verdict.')))
