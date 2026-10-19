#!/usr/bin/env python3
"""Offline, read-only byte/identity verifier. Requires a caller-supplied detached anchor.
Original code: MIT. No mathematical or contribution verdict is produced.
"""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
STATUS_SHA256 = '08a432312fbd0d9d6c3a40d4d835d1f5cd63add3887454f2c5c9c4236e7c39c8'
PRIMARY = {
 'lawler-sheffield': ('https://arxiv.org/html/0906.3804v2','failed'),
 'gigli-tamanini': ('https://arxiv.org/html/1802.02463v3','failed'),
 'pratelli-bisobolev': ('https://arxiv.org/html/1509.01045v1','success'),
 'lawler-sheffield-pdf': ('https://arxiv.org/pdf/0906.3804v2','failed'),
 'han-monotonicity': ('https://arxiv.org/pdf/1710.07953v2','success'),
 'campbell-smoothing': ('https://arxiv.org/html/2507.02854v1','success'),
 'pratelli-readable': (None,'derived'),
 'lawler-sheffield-author': ('https://www.math.uchicago.edu/~lawler/natural.pdf','success'),
 'lawler-zhou': ('https://arxiv.org/pdf/1006.4936v2','success'),
 'haddad': ('https://arxiv.org/pdf/1904.10427v6','success'),
}

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def safe_rel(s):
    require(isinstance(s,str) and s and '\\' not in s, 'unsafe-path')
    p = PurePosixPath(s)
    require(not p.is_absolute() and '..' not in p.parts and '.' not in p.parts
            and str(p)==s, 'unsafe-path')
    return s

def parse(data):
    def unique(items):
        out={}
        for k,v in items:
            require(k not in out, 'duplicate-json-key')
            out[k]=v
        return out
    return json.loads(data, object_pairs_hook=unique)

def snapshot(root):
    dirs={}; files={}
    require(stat.S_ISDIR(root.lstat().st_mode) and not root.is_symlink(), 'root-type')
    for cur, names, leaves in os.walk(root, followlinks=False):
        for name in sorted(names+leaves):
            p=Path(cur)/name; s=p.lstat(); rel=p.relative_to(root).as_posix()
            safe_rel(rel)
            require(not stat.S_ISLNK(s.st_mode), 'symlink')
            if stat.S_ISDIR(s.st_mode):
                dirs[rel]=stat.S_IMODE(s.st_mode)
            else:
                require(stat.S_ISREG(s.st_mode), 'object-type')
                require(s.st_nlink==1, 'hardlink')
                files[rel]={'sha256':digest(p.read_bytes()),'bytes':s.st_size,
                            'mode':stat.S_IMODE(s.st_mode)}
    return dirs,files

def verify(root, anchor):
    require(re.fullmatch('[0-9a-f]{64}', anchor) is not None, 'external-anchor-format')
    require(not root.is_symlink(), 'root-type')
    m=root/'manifest.json'; st=m.lstat()
    require(stat.S_ISREG(st.st_mode) and st.st_nlink==1, 'manifest-type')
    require(stat.S_IMODE(st.st_mode)==0o644, 'manifest-mode')
    raw=m.read_bytes()
    require(digest(raw)==anchor, 'external-anchor-mismatch')
    manifest=parse(raw)
    require(manifest['format']=='r112-exact-inventory-v1' and manifest['pin']==PIN,
            'manifest-format')
    dirs,files=snapshot(root)
    require(dirs==manifest['directories'], 'directory-inventory')
    files.pop('manifest.json')
    require(set(files)==set(manifest['files']), 'file-inventory')
    for rel,meta in manifest['files'].items():
        safe_rel(rel)
        require(files[rel]==meta, 'file-integrity:'+rel)
    def data(rel):
        safe_rel(rel); require(rel in files, 'unlisted-receipt-file')
        return (root/rel).read_bytes()
    def document(rel): return parse(data(rel))
    require(digest(data('public/status.json'))==STATUS_SHA256, 'original-status')
    status=document('public/status.json')
    require(status['target_frozen'] is False and status['nominee'] is None
            and status['state']=='BOUNDED_PREFREEZE_SCREEN_NO_NOMINEE', 'status-scope')
    require(not any('frozen-target' in k or 'original-scope' in k for k in files), 'unexpected-freeze')
    tree=document('private/context/selected-tree.json')
    require(tree['complete_tree_sha256']==TREE_SHA256 and tree['complete_entries']==13223
            and tree['complete_truncated'] is False
            and tree['tree_sha']=='df0564b2deaab87e07854b6344d8c2f037682e77', 'complete-tree-identity')
    entries=tree['entries']; idx={e['path']:e for e in entries}
    require(len(idx)==len(entries)==59, 'selected-tree-inventory')
    receipts=document('private/upstream/receipts.json'); seen=set()
    require(len(receipts)==59, 'source-receipt-count')
    for r in receipts:
        path=safe_rel(r['tree_path']); e=idx[path]
        require(path not in seen, 'duplicate-source'); seen.add(path)
        require(r['status']=='success' and e['type']=='blob' and e['mode']=='100644', 'source-type')
        require(r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+path,
                'canonical-raw-url')
        require(r['file']=='private/upstream/'+path and r['tree_blob']==e['sha'], 'source-binding')
        raw=data(r['file'])
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(blob==e['sha'] and digest(raw)==r['sha256'] and len(raw)==r['bytes']==e['size'],
                'source-digest')
        require(isinstance(r['semantic_read'],bool) and bool(r['reading_extent']), 'source-reading-limit')
    require(seen==set(idx), 'source-tree-coverage')
    prs=document('private/primary/receipts.json'); seen=set()
    for r in prs:
        ident=r['id']; require(ident in PRIMARY and ident not in seen, 'primary-inventory'); seen.add(ident)
        url,kind=PRIMARY[ident]
        require(r.get('requested_url')==url and r['status']==kind, 'primary-identity')
        if kind=='failed':
            require(bool(r.get('error')) and 'file' not in r and r['semantic_read'] is False,
                    'failed-primary-reading')
        else:
            raw=data(r['file']); require(digest(raw)==r['sha256'] and len(raw)==r['bytes'], 'primary-digest')
            require(r['file'].startswith('private/primary/'), 'primary-location')
            if kind=='success':
                require(r.get('final_url')==url, 'primary-final-url')
                require(digest(data(r['text_file']))==r['text_sha256'], 'primary-text-digest')
            else:
                require(r['derived_from']=='private/primary/pratelli-bisobolev.html', 'derived-primary')
        require(bool(r['reading_extent']), 'primary-reading-limit')
    require(seen==set(PRIMARY), 'primary-inventory')
    return {'integrity':'VERIFIED','mathematical_gate':None,'contribution_gate':None,
            'files_excluding_manifest':len(files),'directories':len(dirs),
            'canonical_source_blobs':len(receipts),'primary_successes':sum(r['status']=='success' for r in prs),
            'manifest_sha256':anchor,'report_sha256':digest(data('public/research-report.md'))}

if __name__=='__main__':
    try:
        require(len(sys.argv)==3, 'usage: verify.py PACKET DETACHED_FINALHASH')
        print(json.dumps(verify(Path(sys.argv[1]).absolute(),sys.argv[2]),sort_keys=True))
    except (ValueError,KeyError,OSError,TypeError) as exc:
        print('REJECTED: '+str(exc),file=sys.stderr)
        sys.exit(1)
