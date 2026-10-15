#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Verify the immutable artifact inventory, source authentication and read slices."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def files():return {str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
def main():
 manifest=json.loads((ROOT/'output-manifest.json').read_text());entries=manifest['files'];expected={x['path'] for x in entries}
 assert files()==expected|{'output-manifest.json','SHA256SUMS'},'Unexpected or missing artifact'
 for row in entries:
  data=(ROOT/row['path']).read_bytes();assert len(data)==row['bytes'] and sha(data)==row['sha256'],row['path']
 sums={}
 for line in (ROOT/'SHA256SUMS').read_text().splitlines():
  digest,path=line.split('  ',1);sums[path]=digest;assert sha((ROOT/path).read_bytes())==digest,path
 assert set(sums)==files()-{'SHA256SUMS'}
 source=json.loads((ROOT/'source-manifest.json').read_text())
 tree=json.loads((ROOT/'inputs/context/sources/preprints-tree.json').read_text());idx={x['path']:x for x in tree['tree']}
 for row in source['entries']:
  if 'path' not in row:continue
  data=(ROOT/row['path']).read_bytes();assert sha(data)==row['sha256']
  if 'upstream_path' in row:
   git=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
   assert git==row['git_blob_sha1']==idx[row['upstream_path']]['sha']
 for row in json.loads((ROOT/'read-manifest.json').read_text())['reads']:
  data=(ROOT/row['path']).read_bytes();assert sha(data)==row['sha256']
  if not row.get('ranges'):continue
  lines=data.decode().splitlines(keepends=True)
  for r in row.get('ranges',[]):assert sha(''.join(lines[r['start_line']-1:r['end_line']]).encode())==r['slice_sha256']
 for c in json.loads((ROOT/'source-contracts.json').read_text())['contracts']:
  r=c['source'];data=(ROOT/r['path']).read_bytes();lines=data.decode().splitlines(keepends=True)
  assert 1<=r['start_line']<=r['end_line']<=len(lines),c['id']
  assert sha(data)==r['file_sha256']
  assert sha(''.join(lines[r['start_line']-1:r['end_line']]).encode())==r['slice_sha256']
 print(json.dumps({'status':'PASS','hashed_artifacts':len(entries),'checksum_entries':len(sums),'source_pin':source['pin'],'proof_gate':'pending independent review','contribution_gate':'pending independent review','manuscript_gate':'pending independent review'},indent=2))
if __name__=='__main__':main()
