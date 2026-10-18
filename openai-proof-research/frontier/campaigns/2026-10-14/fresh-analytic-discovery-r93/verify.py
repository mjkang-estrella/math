#!/usr/bin/env python3
"""Identity and scope bookkeeping only. Original code MIT."""
import argparse,hashlib,json,pathlib
p=argparse.ArgumentParser();p.add_argument('--manifest-sha256',required=True);p.add_argument('--repo',type=pathlib.Path,required=True);p.add_argument('--private',action='store_true');a=p.parse_args()
r=pathlib.Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
def need(ok,msg):
 if not ok: raise SystemExit(msg)
mbytes=(r/'MANIFEST.json').read_bytes();need(h(mbytes)==a.manifest_sha256,'external manifest mismatch');m=json.loads(mbytes)
need(m['status']=='unresolved-pre-freeze' and m['scope_frozen'] is False and m['accepted'] is False and m['published'] is False and m['count_change']==0,'status mismatch')
files={str(q.relative_to(r)) for q in r.rglob('*') if q.is_file() and 'private' not in q.relative_to(r).parts and '__pycache__' not in q.relative_to(r).parts and q.name!='MANIFEST.json'}
need(files==set(m['files']),'public inventory mismatch')
for name,sha in m['files'].items(): need(h((r/name).read_bytes())==sha,'payload mismatch: '+name)
need(m['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','pin mismatch')
up=json.loads((a.repo/'sources/upstream.json').read_text());need(up['commit']==m['pin'],'upstream mismatch')
tree={z['path']:z for z in json.loads((a.repo/'sources/preprints-tree.json').read_text())['tree']}
rows=json.loads((r/'source-receipts.json').read_text())+json.loads((r/'source144-receipts.json').read_text());need(len(rows)==79 and len({z['path'] for z in rows})==79,'source inventory mismatch')
for z in rows:
 blob=z.get('blob',z.get('git_blob'));need(tree.get(z['path'],{}).get('sha')==blob,'canonical blob mismatch')
 if a.private:
  b=(r/'private'/z['path']).read_bytes();need(h(b)==z['sha256'],'private source SHA mismatch');need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob,'private Git blob mismatch')
if a.private:
 for z in json.loads((r/'primary-receipts.json').read_text()):
  b=(r/z['path']).read_bytes();need(len(b)==z['bytes'] and h(b)==z['sha256'],'private primary mismatch')
print(json.dumps({'status':'IDENTITIES_ONLY_PASS','public_files':len(files),'canonical_blobs':len(rows),'private_bytes_checked':a.private,'mathematical_verdict':None,'count_change':0}))
