#!/usr/bin/env python3
"""Read-only packet verification. All three anchors must be supplied explicitly."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
EXCEPTIONS=[
'frontier/campaigns/2026-10-14/discovery-arithmetic-r162bo-parent/contribution-intake/assessment.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bo/STATEMENT.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bo/PROOF.md',
'frontier/campaigns/2026-10-14/arithmetic-r162bo-contribution-r1/private/ASSESSMENT.md',
'frontier/campaigns/2026-10-14/arithmetic-r162bo-contribution-r1/private/READING-LIMITS.md']
def sha(b): return hashlib.sha256(b).hexdigest()
def gitsha(kind,b):return hashlib.sha1(kind.encode()+b' '+str(len(b)).encode()+b'\0'+b).hexdigest()
def safe(s):
    assert isinstance(s,str) and s and '\\' not in s
    p=PurePosixPath(s)
    assert not p.is_absolute() and all(x not in ('','..','.') for x in s.split('/')) and str(p)==s
    return s
def inventory(root):
    files=[];dirs=[]
    assert root.is_dir() and not root.is_symlink()
    def visit(p,rel):
        dirs.append({'path':rel,'mode':p.lstat().st_mode})
        for q in sorted(p.iterdir(),key=lambda x:x.name):
            s=(rel+'/' if rel else '')+q.name;safe(s);m=q.lstat().st_mode
            assert not stat.S_ISLNK(m),s
            if stat.S_ISDIR(m):visit(q,s)
            else:
                assert stat.S_ISREG(m),s
                b=q.read_bytes();files.append({'path':s,'mode':m,'bytes':len(b),'sha256':sha(b)})
    visit(root,'')
    return sorted(files,key=lambda x:x['path']),sorted(dirs,key=lambda x:x['path'])
def bindings(root):
    assert json.loads((root/'private/direct-upstream.json').read_text())['commit']==PIN
    tree=json.loads((root/'private/source-tree.json').read_text())
    assert len(tree)==26 and len({x['path'] for x in tree})==26
    entries={x['path']:x for x in tree}
    rec=json.loads((root/'private/source-bindings.json').read_text())
    assert len(rec)==18 and {x['path'] for x in rec}=={x['path'] for x in tree if x['type']=='blob'}
    for x in rec:
        p=safe(x['path']); e=entries[p];b=(root/'private'/p).read_bytes()
        assert len(b)==e['size']==x['bytes']
        assert gitsha('blob',b)==e['sha']==x['git_blob'] and sha(b)==x['sha256']
        assert x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+p
    for p,e in entries.items():
        if e['type']!='tree':continue
        children=[x for x in tree if str(PurePosixPath(x['path']).parent)==p]
        children.sort(key=lambda x:PurePosixPath(x['path']).name+('/' if x['type']=='tree' else ''))
        body=b''.join(x['mode'].lstrip('0').encode()+b' '+PurePosixPath(x['path']).name.encode()+b'\0'+bytes.fromhex(x['sha']) for x in children)
        assert gitsha('tree',body)==e['sha'],p
    copied=json.loads((root/'private/completed-bindings.json').read_text())
    assert len(copied)==5 and [x['path'] for x in copied]==EXCEPTIONS
    for x in copied:
        for p in [PROJECT/x['path'],root/safe(x['copy'])]:
            assert not p.is_symlink() and p.stat().st_mode==x['mode']
            b=p.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'],str(p)
    prim=json.loads((root/'private/primary-acquisition.json').read_text())
    assert len(prim)==5 and {x['name'] for x in prim}=={'bh','gms','craciun','toric','ht'}
    for x in prim:
        p=root/'private/primary'/(x['name']+'.pdf');b=p.read_bytes()
        assert len(b)==x['bytes'] and sha(b)==x['sha256']
        assert sha(p.with_suffix('.txt').read_bytes())==x['extract_sha256']
def verify(root,final_anchor,manifest_anchor,report_anchor):
    assert root.is_dir() and not root.is_symlink()
    for name in ['MANIFEST.json','REPORT.md']:
        assert (root/name).lstat().st_mode==(stat.S_IFREG|0o644),'detached full mode'
    assert stat.S_ISREG((root/'FINAL.md').lstat().st_mode)
    for name,a in [('FINAL.md',final_anchor),('MANIFEST.json',manifest_anchor),('REPORT.md',report_anchor)]:
        assert len(a)==64 and all(c in '0123456789abcdef' for c in a)
        assert sha((root/name).read_bytes())==a,'detached '+name
    m=json.loads((root/'MANIFEST.json').read_text())
    assert m['format']=='r162bp-exact-v1'
    assert m['excluded']==['MANIFEST.json','REPORT.md']
    files,dirs=inventory(root)
    expected=m['files'];names=[x['path'] for x in expected]
    assert names==sorted(names) and len(set(names))==len(names)
    for n in names:safe(n)
    assert [x['path'] for x in m['directories']]==sorted(set(x['path'] for x in m['directories']))
    assert [x for x in files if x['path'] not in m['excluded']]==expected,'exact files/bytes/modes'
    assert dirs==m['directories'],'exact directory modes'
    report=(root/'REPORT.md').read_text()
    assert final_anchor in report and manifest_anchor in report
    if m['binding_policy']=='r162bp':bindings(root)
    else:assert m['binding_policy']=='generic-copied-control'
    return {'payload_files':len(expected),'all_files':len(files),'directories':len(dirs),'payload_bytes':sum(x['bytes'] for x in expected)}
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True)
    for s in ['final','manifest','report']:a.add_argument('--'+s+'-sha256',required=True)
    x=a.parse_args();print(json.dumps(verify(x.root,x.final_sha256,x.manifest_sha256,x.report_sha256),sort_keys=True))
