#!/usr/bin/env python3
"""Read-only externally anchored identity verifier. No mathematical verdict."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);p.add_argument('--repo',required=True);p.add_argument('--private-root');a=p.parse_args()
r=Path(__file__).resolve().parent;repo=Path(a.repo).resolve();private=Path(a.private_root).resolve() if a.private_root else repo/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r104/private'
def sha(b):return hashlib.sha256(b).hexdigest()
def need(ok,reason):
 if not ok:raise SystemExit('FAIL: '+reason)
m=r/'MANIFEST.json';need(sha(m.read_bytes())==a.anchor,'external manifest anchor');j=json.loads(m.read_text())
actual={str(x.relative_to(r)) for x in r.rglob('*') if x.is_file() and 'private' not in x.relative_to(r).parts[:1]}
need(actual==set(j['files'])|{'MANIFEST.json'},'exact public membership')
for name,h in j['files'].items():
 need(not Path(name).is_absolute() and '..' not in Path(name).parts,'safe manifest path')
 need(sha((r/name).read_bytes())==h,'payload '+name)
s=json.loads((r/'source-receipts.json').read_text());tb=(repo/'sources/preprints-tree.json').read_bytes();need(sha(tb)==s['tree_sha256'],'complete tree anchor');t=json.loads(tb)
need(len(t['tree'])==13223 and not t.get('truncated',False),'complete tree size/truncation');need(json.loads((repo/'sources/upstream.json').read_text())['commit']==s['pin'],'immutable source pin')
for f in s['files']:
 match=[e for e in t['tree'] if e['path']==f['path']];need(len(match)==1 and match[0]['sha']==f['git_blob'] and match[0]['type']=='blob','canonical membership '+f['path'])
 b=(private/f['path']).read_bytes();need(sha(b)==f['sha256'],'source SHA '+f['path']);need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==f['git_blob'],'source Git '+f['path'])
for f in json.loads((r/'primary-receipts.json').read_text()):
 for field,hfield in [('file','sha256'),('text_file','text_sha256')]:
  b=(private/'primary'/Path(f[field]).name).read_bytes();need(sha(b)==f[hfield],'primary '+Path(f[field]).name)
need(sha((r/'scope-freeze.md').read_bytes())=='8e9b3f5f30e02e91e8e49010350c07bb8dff845c806e506e8e5b598bed37589e','unchanged full scope')
print(json.dumps({'status':'PASS','payload_files':len(j['files']),'canonical_blobs':len(s['files']),'primary_pdf_and_text_pairs':3,'scope':'identity only; author candidate T298P, no mathematical or contribution verdict'}))
