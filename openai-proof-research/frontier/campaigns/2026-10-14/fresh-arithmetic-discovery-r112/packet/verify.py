"""Read-only exact-membership verifier. Detached anchors MUST be supplied externally.

This checks artifacts, not mathematics, reading, isolation, novelty or acceptance.
Reduced fixtures have their own manifests; original authentication is not inferred.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath

def digest(b): return hashlib.sha256(b).hexdigest()

def check(condition, message):
    if not condition: raise ValueError(message)

def safe_read(root, name):
    p=PurePosixPath(name)
    check(not p.is_absolute() and '..' not in p.parts and str(p)==name,'unsafe path')
    cur=root
    for component in p.parts:
        cur=cur/component
        check(not cur.is_symlink(),'symlink: '+name)
    return cur.read_bytes()

def inventory(root):
    files=[]; dirs=[]
    for current,subdirs,names in os.walk(root,followlinks=False):
        for name in subdirs+names:
            p=Path(current)/name
            check(not p.is_symlink(),'symlink in payload')
        dirs += [str((Path(current)/x).relative_to(root)) for x in subdirs]
        files += [str((Path(current)/x).relative_to(root)) for x in names]
    return sorted(files),sorted(dirs)

def verify(root, anchors):
    check(root.is_dir() and not root.is_symlink(),'bad root')
    check(set(p.name for p in root.iterdir())=={'FINAL.json','MANIFEST.json','REPORT.md','packet'},'outside membership')
    for name,anchor in anchors.items():
        check(len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor),'bad anchor')
        check(digest(safe_read(root,name))==anchor,'detached mismatch: '+name)
    outer=json.loads(safe_read(root,'MANIFEST.json'))
    final=json.loads(safe_read(root,'FINAL.json'))
    check(outer['schema']=='r112-outside-v1','outer schema')
    for name in ['FINAL.json','REPORT.md','packet/MANIFEST.json']:
        b=safe_read(root,name); rec=outer['bound'][name]
        check(len(b)==rec['size'] and digest(b)==rec['sha256'],'outside binding: '+name)
    check(final['payload_manifest_sha256']==outer['bound']['packet/MANIFEST.json']['sha256'],'final payload binding')
    check(final['report_sha256']==anchors['REPORT.md'],'final report binding')
    payload=root/'packet'; m=json.loads(safe_read(payload,'MANIFEST.json'))
    check(m['schema']=='r112-payload-v1','payload schema')
    files,dirs=inventory(payload)
    names=[x['path'] for x in m['files']]
    check(len(names)==len(set(names)),'duplicate payload entry')
    check(files==sorted(names+['MANIFEST.json']) and dirs==m['directories'],'payload membership')
    for rec in m['files']:
        b=safe_read(payload,rec['path'])
        check(len(b)==rec['size'] and digest(b)==rec['sha256'],'payload digest: '+rec['path'])
    kind=final['kind']
    check(kind in ['research_packet','reduced_fixture'],'unknown kind')
    if kind=='research_packet':
        treebytes=safe_read(payload,'private/context/2-preprints-tree.json')
        check(digest(treebytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','tree anchor')
        tree=json.loads(treebytes)
        check(len(tree['tree'])==13223 and tree['truncated'] is False,'tree completeness metadata')
        entries={x['path']:x for x in tree['tree']}
        records=json.loads(safe_read(payload,'private/source/metadata.json'))
        check(len(records)==42 and len({x['path'] for x in records})==42,'source count')
        for rec in records:
            path=rec['path']; b=safe_read(payload,rec['local']); t=entries[path]
            check(rec['local']=='private/source/'+path,'source local path')
            check(rec['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+path,'source pin/path')
            blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            check(len(b)==rec['size']==t['size'] and blob==rec['git_blob']==t['sha'] and digest(b)==rec['sha256'],'source authentication')
        snapshots=json.loads(safe_read(payload,'private/context/original-snapshots.json'))
        for rec in snapshots['records']:
            check(digest(safe_read(payload,rec['copy']))==rec['copy_sha256'],'named-copy snapshot')
        for name in ['CM2011','Dumnicki2007','CM1998v1','DJ2005v1','Dumnicki2005v1','FujinoKV']:
            rec=json.loads(safe_read(payload,'private/primary/'+name+'.json'))
            check(digest(safe_read(payload,'private/primary/'+name+'.pdf'))==rec['pdf_sha256'],'primary PDF bytes')
            check(digest(safe_read(payload,'private/primary/'+name+'.txt'))==rec['text_sha256'],'primary extraction bytes')
    return {'artifact_integrity':'matched','kind':kind,'payload_files':len(names),
            'original_source_authentication':kind=='research_packet',
            'mathematical_gate':False,'isolation_certificate':False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,required=True)
    for name in ['final','manifest','report']:p.add_argument('--'+name+'-sha',required=True)
    a=p.parse_args()
    anchors={'FINAL.json':a.final_sha,'MANIFEST.json':a.manifest_sha,'REPORT.md':a.report_sha}
    try: print(json.dumps(verify(a.root,anchors),sort_keys=True))
    except (ValueError,KeyError,OSError,TypeError,json.JSONDecodeError) as e:
        p.exit(1,'REJECTED: '+str(e)+'\n')

if __name__=='__main__': main()
