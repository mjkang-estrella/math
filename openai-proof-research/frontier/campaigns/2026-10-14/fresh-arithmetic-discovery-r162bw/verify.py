#!/usr/bin/env python3
"""Read-only artifact verifier. No mathematical claims or gates."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PREFIX='preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026'
EXCEPTIONS={
'frontier/campaigns/2026-10-14/discovery-arithmetic-r162bv-parent/assessment.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bv/private/DERIVATION.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bv/WORKING.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bv/private/READING-LIMITS.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bv/FINAL.md'}

def sha(b):return hashlib.sha256(b).hexdigest()
def check(ok,why):
    if not ok:raise ValueError(why)
def safe(s,root_ok=False):
    if root_ok and s=='.':return
    p=PurePosixPath(s)
    check(isinstance(s,str) and s and not p.is_absolute() and str(p)==s and '\\' not in s and all(x not in ('','.','..') for x in p.parts),'unsafe path')
def inventory(root):
    files=[];dirs=[]
    def descend(p):
        st=p.lstat();check(stat.S_ISDIR(st.st_mode),'directory type')
        rel='.' if p==root else p.relative_to(root).as_posix()
        dirs.append({'path':rel,'mode':st.st_mode})
        for e in sorted(os.scandir(p),key=lambda x:x.name):
            q=Path(e.path);t=q.lstat();check(not stat.S_ISLNK(t.st_mode),'symlink')
            if stat.S_ISDIR(t.st_mode):descend(q)
            else:
                check(stat.S_ISREG(t.st_mode),'special file')
                n=q.relative_to(root).as_posix();safe(n)
                b=q.read_bytes();files.append({'path':n,'mode':t.st_mode,'bytes':len(b),'sha256':sha(b)})
    descend(root)
    return sorted(files,key=lambda x:x['path']),sorted(dirs,key=lambda x:x['path'])
def source_checks(root,project):
    es=json.loads((root/'private/source-bindings.json').read_bytes())
    check(len(es)==19 and len({x['path'] for x in es})==19,'source selection')
    check(all(x['path']==PREFIX or x['path'].startswith(PREFIX+'/') for x in es),'source prefix')
    au=json.loads((root/'private/source-authentication.json').read_bytes())
    check(au['pin']==PIN and au['tree_bytes']==4858136 and au['tree_entries']==13223 and au['tree_sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','pin/tree binding')
    records={x['path']:x for x in au['blobs']};check(len(records)==len(au['blobs'])==15,'source records')
    for e in es:
        if e['type']=='blob':
            n='private/source/'+e['path'][len(PREFIX)+1:];p=root/n;b=p.read_bytes();r=records[e['path']]
            g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            check(len(b)==e['size']==r['bytes'] and g==e['sha']==r['git_blob'],'source blob')
            check(r['local']==n and sha(b)==r['sha256'] and p.stat().st_mode==r['mode'],'source local binding')
            check(r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path'],'source URL')
        else:
            check(e['type']=='tree','source type')
            children=[z for z in es if str(PurePosixPath(z['path']).parent)==e['path']]
            children.sort(key=lambda z:PurePosixPath(z['path']).name+('/' if z['type']=='tree' else ''))
            body=b''.join(z['mode'].lstrip('0').encode()+b' '+PurePosixPath(z['path']).name.encode()+b'\0'+bytes.fromhex(z['sha']) for z in children)
            check(hashlib.sha1(b'tree '+str(len(body)).encode()+b'\0'+body).hexdigest()==e['sha'],'source tree')
    cs=json.loads((root/'private/context/bindings.json').read_bytes())
    check(len(cs)==5 and {x['original'] for x in cs}==EXCEPTIONS,'permitted original set')
    for c in cs:
        safe(c['copy']);original=project/c['original'];copy=root/c['copy']
        check(stat.S_ISREG(original.lstat().st_mode) and stat.S_ISREG(copy.lstat().st_mode),'copy type')
        a=original.read_bytes();b=copy.read_bytes()
        check(a==b and len(a)==c['size'] and sha(a)==c['sha256'],'original/copy bytes')
        check(original.stat().st_mode==c['original_mode_later'] and copy.stat().st_mode==c['copy_mode'],'original/copy full modes')
    count=0
    for fn in ['acquisition.json','acquisition2.json']:
        for a in json.loads((root/'private/primary'/fn).read_bytes()):
            if 'error' in a:continue
            safe(a['name']);p=root/'private/primary'/(a['name']+'.pdf');b=p.read_bytes()
            check(len(b)==a['bytes'] and sha(b)==a['sha256'],'primary bytes');count+=1
    check(count==7,'primary count')

def validate(root,final_anchor,manifest_anchor,report_anchor,project,manifest_bytes=None,report_bytes=None,preflight=False):
    root=Path(root)
    mb=manifest_bytes if manifest_bytes is not None else (root/'MANIFEST.json').read_bytes()
    rb=report_bytes if report_bytes is not None else (root/'REPORT.md').read_bytes()
    fb=(root/'FINAL.md').read_bytes()
    for b,a,n in [(fb,final_anchor,'FINAL'),(mb,manifest_anchor,'MANIFEST'),(rb,report_anchor,'REPORT')]:
        check(len(a)==64 and all(c in '0123456789abcdef' for c in a),'anchor format')
        check(sha(b)==a,n+' detached anchor')
    m=json.loads(mb);report=json.loads(rb)
    check(m['schema']=='r162bw-packet-v1' and m['kind'] in ['research','tiny-control'],'schema')
    check(report['FINAL_SHA256']==final_anchor and report['MANIFEST_SHA256']==manifest_anchor,'report binding')
    fs=m['files'];ds=m['directories']
    for rows,root_ok in [(fs,False),(ds,True)]:
        names=[x['path'] for x in rows]
        check(names==sorted(names) and len(names)==len(set(names)),'sorted unique records')
        for n in names:safe(n,root_ok)
    check(all(x['path'] not in ['MANIFEST.json','REPORT.md'] for x in fs),'detached membership')
    actual_f,actual_d=inventory(root)
    rest=[x for x in actual_f if x['path'] not in ['MANIFEST.json','REPORT.md']]
    check(rest==fs,'exact file membership/hash/length/full mode')
    check(actual_d==ds,'exact directory membership/full mode')
    for n in ['MANIFEST.json','REPORT.md']:
        p=root/n
        if p.exists():check(p.lstat().st_mode==m['detached_modes'][n],'detached full mode')
        else:check(preflight,'missing detached artifact')
    check(report['payloads']==len(fs),'report payload count')
    if m['kind']=='research':source_checks(root,Path(project))
    return {'artifact':'MATCH','payloads':len(fs),'directories':len(ds),'payload_bytes':sum(x['bytes'] for x in fs),'mathematical_gate':False}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',default=str(Path(__file__).resolve().parent))
    p.add_argument('--project',default='/home/mj-kang/Documents/Dev/math/openai-proof-research')
    p.add_argument('--final',required=True);p.add_argument('--manifest',required=True);p.add_argument('--report',required=True)
    a=p.parse_args()
    print(json.dumps(validate(Path(a.root),a.final,a.manifest,a.report,Path(a.project)),sort_keys=True))
