#!/usr/bin/env python3
"""Read-only artifact verifier. No network, writes, or mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

DETACHED = {'MANIFEST.json', 'REPORT.md'}
EXCEPTIONS = [
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162bk-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bk/private/COMPARISON.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bk/private/WORKING.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bk/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bk/FINAL.md',
]
PREFIXES = [
 'preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026',
 'preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026',
]
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_HASH = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def require(ok, why):
    if not ok:
        raise ValueError(why)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def safe(p):
    require(isinstance(p, str) and p and p != '.' and '\\' not in p, 'invalid path')
    q = PurePosixPath(p)
    require(not q.is_absolute() and '..' not in q.parts and '.' not in q.parts
            and q.as_posix() == p, 'unsafe or noncanonical path: '+p)
    return p

def inventory(root):
    root = Path(root)
    require(stat.S_ISDIR(root.lstat().st_mode), 'root must be actual directory')
    files, dirs = {}, {'.': oct(root.lstat().st_mode)}
    def walk(base):
        for p in sorted(base.iterdir()):
            rel = safe(p.relative_to(root).as_posix())
            mode = p.lstat().st_mode
            if stat.S_ISDIR(mode):
                dirs[rel] = oct(mode)
                walk(p)
            elif stat.S_ISREG(mode):
                files[rel] = oct(mode)
            else:
                raise ValueError('nonregular entry: '+rel)
    walk(root)
    return files, dirs

def verify(root, anchors, project=None, overrides=None):
    """overrides permits ONLY absent detached files for identical preseal logic."""
    root = Path(root)
    overrides = overrides or {}
    require(set(overrides) <= DETACHED, 'invalid preflight overrides')
    files, dirs = inventory(root)
    for p in overrides:
        require(p not in files, 'preflight must not replace an existing file')
        files[p] = '0o100644'
    def read(p):
        safe(p)
        return overrides[p] if p in overrides else (root/p).read_bytes()
    require(set(anchors) == {'FINAL.md', 'MANIFEST.json', 'REPORT.md'}, 'three anchors required')
    for name, digest in anchors.items():
        require(isinstance(digest,str) and len(digest)==64 and all(c in '0123456789abcdef' for c in digest), 'bad anchor format')
        require(sha(read(name)) == digest, 'anchor mismatch: '+name)
    m = json.loads(read('MANIFEST.json'))
    require(m['version'] == 1, 'manifest version')
    records = m['files']
    paths = [safe(x['path']) for x in records]
    require(paths == sorted(paths) and len(set(paths)) == len(paths), 'unsorted or duplicate files')
    require(set(paths) == set(files)-DETACHED, 'exact file membership mismatch')
    for x in records:
        b = read(x['path'])
        require(len(b)==x['bytes'] and sha(b)==x['sha256'], 'payload mismatch: '+x['path'])
        require(files[x['path']]==x['mode'], 'file mode mismatch: '+x['path'])
    dpaths = [x['path'] for x in m['directories']]
    require(dpaths==sorted(dpaths) and len(set(dpaths))==len(dpaths), 'unsorted or duplicate directories')
    for p in dpaths:
        if p != '.': safe(p)
    require({x['path']:x['mode'] for x in m['directories']} == dirs, 'directory membership/mode mismatch')
    require(m['detached_modes']=={p:files[p] for p in sorted(DETACHED)}, 'detached modes mismatch')
    report = read('REPORT.md').decode('utf-8')
    require('FINAL_SHA256='+anchors['FINAL.md'] in report and 'MANIFEST_SHA256='+anchors['MANIFEST.json'] in report, 'report anchor cross-binding')
    if m.get('bindings') == 'r162bl':
        require(project is not None, 'explicit --project required for external bindings')
        project = Path(project)
        raw = (project/'sources/preprints-tree.json').read_bytes()
        require(len(raw)==4858136 and sha(raw)==TREE_HASH, 'complete tree binding')
        tree = json.loads(raw)
        require(len(tree['tree'])==13223 and tree['truncated'] is False, 'complete tree structure')
        for prefix,selection,binding,expected in zip(PREFIXES,['tree-selection.json','companion-tree.json'],['source-bindings.json','companion-bindings.json'],[10,14]):
            rows = [x for x in tree['tree'] if x['path']==prefix or x['path'].startswith(prefix+'/')]
            require(json.loads(read('private/'+selection))==rows, 'selected tree binding')
            blobs = {x['path']:x for x in rows if x['type']=='blob'}
            bs = json.loads(read('private/'+binding))
            require(len(bs)==expected and {x['path'] for x in bs}==set(blobs), 'canonical blob membership')
            for x in bs:
                meta=blobs[x['path']]
                require(all(x[k]==meta[k] for k in ['mode','type','sha','size']), 'Git metadata mismatch')
                require(x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path'], 'pinned URL mismatch')
                b=read(safe(x['local']))
                require(len(b)==x['size'] and sha(b)==x['sha256'], 'canonical payload mismatch')
                require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['sha'], 'Git blob mismatch')
        initial = json.loads(read('private/completed-bindings.json'))
        later = json.loads(read('private/completed-later-modes.json'))['records']
        require([x['path'] for x in initial]==EXCEPTIONS and [x['path'] for x in later]==EXCEPTIONS, 'exact exception list required')
        for x,y in zip(initial,later):
            require(all(y[k]==v for k,v in x.items()), 'initial/later binding changed')
            p=project/x['path']; mode=p.lstat().st_mode
            require(stat.S_ISREG(mode), 'nonregular completed original')
            b=p.read_bytes(); c=read(x['copy'])
            require(b==c and len(b)==x['bytes'] and sha(b)==x['sha256'], 'original/copy mismatch')
            require(oct(mode&0o7777)==x['mode'] and oct(mode)==y['full_mode'], 'original modes mismatch')
            require(files[x['copy']]==y['copy_full_mode'], 'copy mode mismatch')
        db=json.loads(read('private/direct-bindings.json'))
        specs=[('frontier/NEW-TEN-2026-10-14.md',4801,6347,'private/acceptance-window.txt'),('sources/CONTENTS.md',239445,240464,'private/catalogue-window.txt')]
        require([(x['path'],x['start'],x['end'],x['copy']) for x in db['slices']]==specs, 'bounded slices only')
        for x in db['slices']:
            with (project/x['path']).open('rb') as f:
                f.seek(x['start']);b=f.read(x['end']-x['start'])
            require(b==read(x['copy']) and sha(b)==x['sha256'], 'bounded slice mismatch')
    else:
        require(m.get('bindings')=='tiny-control', 'unknown binding scope')
    return {'result':'MATCH','payload_files':len(records),'payload_bytes':sum(x['bytes'] for x in records),'whole_files':len(files),'directories_including_root':len(dirs)}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root');ap.add_argument('final_sha256');ap.add_argument('manifest_sha256');ap.add_argument('report_sha256');ap.add_argument('--project')
    a=ap.parse_args()
    result=verify(a.root,{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256},a.project)
    print(json.dumps(result,sort_keys=True))

if __name__=='__main__':
    main()
