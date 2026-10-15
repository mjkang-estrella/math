"""Verify pinned H bytes; optionally retrieve missing bytes into a disposable cache.
Copyright (c) 2026 Myeongjin Kang. MIT License.
Never writes to the shared source directory.
"""
from pathlib import Path
import argparse,hashlib,json,tempfile,urllib.request
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--project-root',type=Path);p.add_argument('--fetch',action='store_true');a=p.parse_args()
if a.project_root is None:
    a.project_root=next((ancestor for ancestor in HERE.parents
                         if (ancestor/'AGENTS.md').is_file()
                         and (ancestor/'sources/upstream.json').is_file()),None)
    if a.project_root is None:
        p.error('Cannot locate project root; pass --project-root /path/to/openai-proof-research')
records=json.loads((HERE/'source-H.json').read_text())['files']
(HERE/'tmp').mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='H-verify-',dir=HERE/'tmp') as temp:
    for r in records:
        src=a.project_root/r['local_path']
        if src.is_file(): data=src.read_bytes()
        elif a.fetch:
            with urllib.request.urlopen(r['raw_url'],timeout=45) as response: data=response.read()
            (Path(temp)/Path(r['local_path']).name).write_bytes(data)
        else: raise SystemExit(f'Missing {src}; use --project-root or --fetch (temporary pinned download)')
        assert len(data)==r['bytes'],r['local_path']
        assert hashlib.sha256(data).hexdigest()==r['sha256'],r['local_path']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==r['git_blob_sha1'],r['local_path']
print(json.dumps({'status':'PASS','pinned_H_files':len(records),'source_truth':'stipulated, not audited','frozen_source_writes':False}))
