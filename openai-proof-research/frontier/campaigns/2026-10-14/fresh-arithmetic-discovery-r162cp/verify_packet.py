"""Read-only exact-packet verifier. All three detached SHA256 anchors are required.
Artifact authentication only; no mathematical review or acceptance is performed.
Run with python -B to prohibit interpreter cache writes.
"""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PREFIX='preprints/Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026'
TREE_HASH='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
FROZEN='ebbecfde0342e866f1401764980ccaf1f3f0c08bc1aea5269e217021774594c9'
ALLOWED={'AGENTS.md','sources/upstream.json',
'frontier/campaigns/2026-10-14/discovery-arithmetic-r162co-parent/assessment.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162co/private/DERIVATION.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162co/private/WORKING.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162co/private/READING-LIMITS.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162co/FINAL.md'}
RESERVED={'MANIFEST.json','REPORT.md'}

def digest(b): return hashlib.sha256(b).hexdigest()
def demand(ok,msg):
    if not ok: raise ValueError(msg)
def safe(s):
    demand(isinstance(s,str) and s and '\\' not in s and '\0' not in s,'unsafe path')
    p=PurePosixPath(s)
    demand(not p.is_absolute() and '..' not in p.parts and '.' not in p.parts and p.as_posix()==s,'unsafe path '+s)
    return s

def inventory(root):
    demand(not root.is_symlink() and root.is_dir(),'bad root')
    files=[];dirs=[{'path':'.','mode':root.stat().st_mode}]
    def visit(p):
        for child in sorted(p.iterdir(),key=lambda x:x.name):
            name=child.relative_to(root).as_posix();safe(name)
            st=child.lstat()
            demand(not stat.S_ISLNK(st.st_mode),'symlink '+name)
            if stat.S_ISDIR(st.st_mode):dirs.append({'path':name,'mode':st.st_mode});visit(child)
            else:
                demand(stat.S_ISREG(st.st_mode),'nonregular '+name)
                files.append(name)
    visit(root)
    return sorted(files),sorted(dirs,key=lambda x:x['path'])

def file_record(root,name):
    safe(name);p=root/name;st=p.lstat();demand(stat.S_ISREG(st.st_mode),'not regular '+name)
    b=p.read_bytes();return {'path':name,'bytes':len(b),'sha256':digest(b),'mode':st.st_mode}

def source_and_copies(root,project):
    ds=json.loads((root/'private/direct/bindings.json').read_text())
    demand(len(ds)==7 and {d['original'] for d in ds}==ALLOWED,'direct scope')
    for d in ds:
        original=project/d['original'];p=root/safe(d['copy'])
        demand(not original.is_symlink() and stat.S_ISREG(original.lstat().st_mode),'direct type')
        raw=original.read_bytes();copy=p.read_bytes()
        demand(raw==copy and len(raw)==d['bytes'] and digest(raw)==d['sha256'],'direct bytes '+d['original'])
        demand(original.stat().st_mode==d['original_mode'] and p.stat().st_mode==d['copy_mode'],'direct full mode')
    for original,start,end,copy in [
        ('frontier/NEW-TEN-2026-10-14.md',4801,6347,'NEW-TEN-2026-10-14.md.window'),
        ('sources/CONTENTS.md',279582,280658,'CONTENTS.md.window')]:
        with (project/original).open('rb') as f:f.seek(start);raw=f.read(end-start)
        demand(len(raw)==end-start and raw==(root/'private/direct'/copy).read_bytes(),'exact window')
    up=json.loads((root/'private/direct/01-upstream.json').read_text())
    demand(up['commit']==PIN and up['repository']=='https://github.com/openai/math','pin')
    # Complete authorized metadata, never the journal or catalogue, is hashed here.
    full=(project/'sources/preprints-tree.json').read_bytes()
    demand(len(full)==4858136 and digest(full)==TREE_HASH,'complete tree anchor')
    obj=json.loads(full);entries=obj['tree'] if isinstance(obj,dict) else obj
    demand(len(entries)==13223,'tree count')
    selected=[e for e in entries if e['path']==PREFIX or e['path'].startswith(PREFIX+'/')]
    tree=json.loads((root/'private/source/tree.json').read_text())
    demand(selected==tree and len(tree)==15,'selected tree equality')
    bs=json.loads((root/'private/source/bindings.json').read_text())
    blob_entries={e['path']:e for e in tree if e['type']=='blob'}
    demand(len(bs)==10 and {b['upstream'] for b in bs}==set(blob_entries),'blob scope')
    for b in bs:
        e=blob_entries[b['upstream']]
        demand(b['path']=='private/source/'+b['upstream'][len(PREFIX)+1:],'blob local path')
        demand(b['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+b['upstream'],'blob pin URL')
        p=root/safe(b['path']);raw=p.read_bytes()
        sha=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        demand(len(raw)==b['bytes']==e['size'] and digest(raw)==b['sha256'] and sha==b['git_blob']==e['sha'],'blob authentication')
        demand(p.stat().st_mode==b['mode'],'blob full mode')
    ts=[e for e in tree if e['type']=='tree'];demand(len(ts)==5,'tree nodes')
    for e in ts:
        kids=[x for x in tree if str(PurePosixPath(x['path']).parent)==e['path']]
        kids.sort(key=lambda x:(PurePosixPath(x['path']).name+('/' if x['type']=='tree' else '')).encode())
        raw=b''.join((x['mode'].lstrip('0')+' '+PurePosixPath(x['path']).name).encode()+b'\0'+bytes.fromhex(x['sha']) for x in kids)
        sha=hashlib.sha1(b'tree '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        demand(sha==e['sha'],'Git tree '+e['path'])
    demand(tree[0]['sha']=='a8290992f2b0d016d03c022202dabadced6b22c5','source root tree')
    fr=json.loads((root/'FREEZE.json').read_text());s=file_record(root,'STATEMENT.md')
    demand(fr['sha256']==s['sha256']==FROZEN and fr['bytes']==s['bytes'] and fr['mode']==s['mode'],'frozen statement')
    # Download metadata must match the exact retained PDFs, including unread ones.
    for b in json.loads((root/'private/primary/bindings.json').read_text()):
        rec=file_record(root,'private/primary/'+b['name']+'.pdf')
        demand(all(rec[k]==b[k] for k in ['bytes','sha256','mode']),'primary binding')
    for name in ['LA','LAv2']:
        b=json.loads((root/'private/primary'/f'{name}-binding.json').read_text())
        rec=file_record(root,'private/primary/'+name+'.pdf')
        demand(all(rec[k]==b[k] for k in ['bytes','sha256','mode']),'LA binding')

def check_material(root,m,project):
    """Identical payload logic used in preflight, tiny controls and sealed verification."""
    demand(m['schema']=='r162cp-exact-packet-1','schema')
    records=m['files'];names=[safe(x['path']) for x in records]
    demand(names==sorted(set(names)),'files must be sorted and unique')
    demand(not set(names)&RESERVED and 'FINAL.md' in names,'reserved/final membership')
    actual,dirs=inventory(root)
    demand(sorted(set(actual)-RESERVED)==names,'exact file membership')
    demand(m['directories']==dirs,'exact directory membership/full modes')
    for x in records:demand(file_record(root,x['path'])==x,'bytes/hash/full mode '+x['path'])
    if m['kind']=='research':source_and_copies(root,project)
    else:demand(m['kind']=='tiny-control','packet kind')
    return {'payloads':len(records),'payload_bytes':sum(x['bytes'] for x in records),'directories_including_root':len(dirs)}

def verify(root,project,final_sha,manifest_sha,report_sha):
    for name,expected in [('FINAL.md',final_sha),('MANIFEST.json',manifest_sha),('REPORT.md',report_sha)]:
        demand(len(expected)==64 and all(c in '0123456789abcdef' for c in expected),'explicit SHA256 anchor')
        demand(file_record(root,name)['sha256']==expected,'detached anchor '+name)
    m=json.loads((root/'MANIFEST.json').read_text())
    for name in RESERVED:demand((root/name).stat().st_mode==m['anchor_modes'][name],'anchor full mode')
    out=check_material(root,m,project)
    return dict(status='MATCH',**out,whole_root_files=out['payloads']+2)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--project',type=Path,required=True)
    ap.add_argument('--final-sha256',required=True);ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--report-sha256',required=True)
    a=ap.parse_args()
    print(json.dumps(verify(a.root,a.project,a.final_sha256,a.manifest_sha256,a.report_sha256),sort_keys=True))
if __name__=='__main__':main()
