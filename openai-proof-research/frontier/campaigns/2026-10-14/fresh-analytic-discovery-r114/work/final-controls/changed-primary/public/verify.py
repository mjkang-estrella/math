#!/usr/bin/env python3
"""MIT. Offline, read-only packet integrity verifier; no mathematical gates."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def require(condition, message):
    if not condition:
        raise ValueError(message)
def sha(data):
    return hashlib.sha256(data).hexdigest()
def safe_name(name):
    require(isinstance(name,str) and name and not name.startswith('/'), 'bad relative path')
    require('\\' not in name and all(p not in ('','.', '..') for p in name.split('/')), 'bad path component')
    return name

def verify(root, anchor):
    require(re.fullmatch('[0-9a-f]{64}', anchor) is not None, 'detached finalhash must be 64 lowercase hex characters')
    root = Path(os.path.abspath(root))
    for ancestor in (root, *root.parents):
        require(not ancestor.is_symlink(), 'symlink in packet root ancestry')
    require(root.is_dir(), 'packet root is not a directory')
    manifest_path = root/'manifest.json'
    ms = manifest_path.lstat()
    require(stat.S_ISREG(ms.st_mode) and ms.st_nlink == 1, 'manifest must be a regular unlinked file')
    raw = manifest_path.read_bytes()
    require(sha(raw) == anchor, 'detached manifest anchor mismatch')
    manifest = json.loads(raw)
    require(manifest['schema'] == 'r114-integrity-v1' and manifest['pin'] == PIN, 'manifest identity')
    entries = manifest['files']
    names = [safe_name(x['path']) for x in entries]
    dirs = [safe_name(x) for x in manifest['directories']]
    require(names == sorted(set(names)) and dirs == sorted(set(dirs)), 'noncanonical inventory')
    require('manifest.json' not in names, 'manifest cannot hash itself')
    actual_files=[]; actual_dirs=[]
    for parent, directory_names, file_names in os.walk(root, followlinks=False):
        for name in directory_names:
            p=Path(parent)/name; st=p.lstat()
            require(stat.S_ISDIR(st.st_mode), 'non-directory or symlink in directory inventory')
            actual_dirs.append(p.relative_to(root).as_posix())
        for name in file_names:
            p=Path(parent)/name; st=p.lstat()
            require(stat.S_ISREG(st.st_mode) and st.st_nlink == 1, 'nonregular file or hardlink')
            actual_files.append(p.relative_to(root).as_posix())
    require(sorted(actual_files) == sorted(names+['manifest.json']), 'exact file inventory mismatch')
    require(sorted(actual_dirs) == dirs, 'exact directory inventory mismatch')
    for row in entries:
        p=root/row['path']; data=p.read_bytes(); st=p.lstat()
        require(len(data)==row['bytes'] and sha(data)==row['sha256'], 'content mismatch: '+row['path'])
        require(stat.S_IMODE(st.st_mode)==row['mode'], 'mode mismatch: '+row['path'])
    status=json.loads((root/'public/status.json').read_bytes())
    require(status['round']=='fresh-analytic-discovery-r114' and status['pin']==PIN, 'status identity')
    require(status['target_frozen'] is False and status['nominee'] is None, 'status scope')
    require(status['mathematical_gate'] is None and status['contribution_rating'] is None, 'unauthorized gate')
    require(status['scope_repair'] is False and status['integrity_is_mathematical_validation'] is False, 'status boundary')
    source_rows=json.loads((root/'private/upstream/receipts.json').read_bytes())
    for row in source_rows:
        local=safe_name(row['local']); data=(root/local).read_bytes(); tree=row['tree_entry']
        require(local.startswith('private/upstream/'), 'source privacy')
        require(tree['path']==row['path'] and tree['type']=='blob', 'selected tree identity')
        require(row['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+row['path'], 'unpinned raw URL')
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(blob==row['git_blob']==tree['sha'], 'source Git identity')
        require(len(data)==row['bytes']==tree['size'] and sha(data)==row['sha256'], 'source bytes')
    primary_rows=json.loads((root/'private/primary/receipts.json').read_bytes())
    successful=0
    for row in primary_rows:
        if row['status']=='ok':
            successful+=1; name=safe_name(row['local'])
            require(name.startswith('private/primary/'), 'primary privacy')
            pdf=(root/name).read_bytes()
            txt=(root/(name+'.txt')).read_bytes()
            require(pdf.startswith(b'%PDF') and len(pdf)==row['bytes'] and sha(pdf)==row['sha256'], 'primary PDF identity')
            require(sha(txt)==row['text_sha256'], 'primary text identity')
        else:
            require(row['status']=='failed' and bool(row['error']), 'failed receipt lacks reason')
    context=json.loads((root/'private/context-receipt.json').read_bytes())
    require(context['tree_entries']==13223 and context['tree_truncated'] is False, 'complete tree receipt')
    trees=[x for x in context['files'] if x['path']=='sources/preprints-tree.json']
    require(len(trees)==1 and trees[0]['sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b', 'tree digest')
    return dict(integrity='verified', mathematical_validation=False, files=len(entries), directories=len(dirs), pinned_sources=len(source_rows), successful_primary_versions=successful, finalhash=anchor, report_sha256=sha((root/'public/research-report.md').read_bytes()))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet',type=Path,default=Path(__file__).absolute().parents[1])
    ap.add_argument('--expect-finalhash',required=True,help='external detached manifest SHA256; never inferred from packet')
    args=ap.parse_args()
    try:
        print(json.dumps(verify(args.packet,args.expect_finalhash),sort_keys=True))
    except Exception as exc:
        print(json.dumps(dict(integrity='rejected',reason=str(exc)),sort_keys=True),file=sys.stderr)
        return 1
    return 0
if __name__=='__main__':
    sys.exit(main())
