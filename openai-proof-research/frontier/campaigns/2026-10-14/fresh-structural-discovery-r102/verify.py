#!/usr/bin/env python3
"""Read-only externally anchored identity verifier; no mathematical verdict."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);p.add_argument('--repo',required=True);a=p.parse_args()
root=Path(__file__).resolve().parent; repo=Path(a.repo).resolve()
def sha(b):return hashlib.sha256(b).hexdigest()
def require(ok,reason):
 if not ok:raise SystemExit('FAIL: '+reason)
m=root/'MANIFEST.json'; require(sha(m.read_bytes())==a.anchor,'external manifest anchor')
d=json.loads(m.read_text()); actual={str(x.relative_to(root)) for x in root.rglob('*') if x.is_file()}
require(actual==set(d['files'])|{'MANIFEST.json'},'exact public membership')
for name,h in d['files'].items():require(sha((root/name).read_bytes())==h,'payload '+name)
l=json.loads((root/'reading-limits.json').read_text()); tb=(repo/'sources/preprints-tree.json').read_bytes();require(sha(tb)==l['complete_tree_verification']['sha256'],'complete tree anchor')
t=json.loads(tb);require(len(t['tree'])==13223 and not t.get('truncated',False),'complete tree size/truncation')
for s in l['canonical_source_reads']:
 matches=[e for e in t['tree'] if e['path']==s['path']];require(len(matches)==1 and matches[0]['sha']==s['git_blob'],'canonical membership '+s['path'])
 b=(repo/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r100/private'/s['path']).read_bytes()
 require(sha(b)==s['sha256'],'source SHA '+s['path'])
 require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==s['git_blob'],'source Git '+s['path'])
print(json.dumps({'status':'PASS','payload_files':len(d['files']),'canonical_blobs':len(l['canonical_source_reads']),'scope':'identity only; conditional author support, r69 unproved'}))
