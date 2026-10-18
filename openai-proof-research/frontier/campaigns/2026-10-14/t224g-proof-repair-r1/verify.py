#!/usr/bin/env python3
"""Read-only repair/dependency identity verifier; no mathematical verdict."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);p.add_argument('--repo',required=True);a=p.parse_args();root=Path(__file__).resolve().parent;repo=Path(a.repo).resolve()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise SystemExit('FAIL: '+msg)
def packet(r,h,label):
 need(sha(r/'MANIFEST.json')==h,label+' external manifest anchor');j=json.loads((r/'MANIFEST.json').read_text())
 actual={str(x.relative_to(r)) for x in r.rglob('*') if x.is_file() and x.relative_to(r).parts[0]!='private' and x.name!='MANIFEST.json'}
 need(actual==set(j['files']),label+' exact public membership')
 for n,s in j['files'].items():
  need(not Path(n).is_absolute() and '..' not in Path(n).parts,'safe payload path');need(sha(r/n)==s,label+' payload '+n)
 return j
m=packet(root,a.anchor,'repair');d=json.loads((root/'anchors.json').read_text());author=repo/d['author_directory'];review=repo/d['review_directory']
packet(author,d['author_manifest_sha256'],'author');packet(review,d['review_manifest_sha256'],'review');need(sha(author/'scope-status.json')==d['scope_sha256'],'original full scope')
need(d['accepted'] is False and d['count_change']==0 and d['contribution']=='TECHNICAL unchanged' and d['independent_repair_gate']=='not requested or supplied','status boundaries')
tree=repo/'sources/preprints-tree.json';need(sha(tree)==d['tree_sha256'],'complete tree anchor');t=json.loads(tree.read_text());need(len(t['tree'])==13223 and not t.get('truncated',False),'complete tree membership count');need(json.loads((repo/'sources/upstream.json').read_text())['commit']==d['pin'],'immutable pin')
for s in d['canonical_interfaces']:
 match=[x for x in t['tree'] if x['path']==s['path']];need(len(match)==1 and match[0]['sha']==s['git_blob'] and match[0]['type']=='blob','canonical source membership')
 b=(author/'private'/s['path']).read_bytes();need(hashlib.sha256(b).hexdigest()==s['sha256'],'canonical source SHA');need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==s['git_blob'],'canonical Git blob')
for kind in ['pdf','text']:need(sha(repo/d['primary'][kind])==d['primary'][kind+'_sha256'],'GPS '+kind+' identity')
print(json.dumps({'status':'PASS_IDENTITY_ONLY','repair_payloads':len(m['files']),'canonical_interfaces':3,'original_scope_unchanged':True,'contribution':'TECHNICAL unchanged','count_change':0,'mathematical_verdict':False}))
