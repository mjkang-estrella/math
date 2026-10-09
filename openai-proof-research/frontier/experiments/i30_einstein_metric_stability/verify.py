#!/usr/bin/env python3
"""Retained-byte and contract integrity audit, separate from a proof audit."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i30_einstein_metric_stability';E=R/'frontier/experiments/i30_einstein_metric_stability'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return (R/p).read_bytes()
errors=[];drift=[];counts={}
def check(ok,msg):
 if not ok:errors.append(msg)
inputs=json.loads((S/'input-manifest.json').read_text())['files']
for x in inputs:
 b=read(x['frozen']);check(sha(b)==x['sha256'] and len(b)==x['bytes'],'frozen input '+x['path'])
 live=sha(read(x['path']))
 if live!=x['sha256']:
  rec=dict(path=x['path'],frozen_sha256=x['sha256'],live_sha256=live)
  if x.get('shared'):drift.append(rec)
  else:errors.append('nonshared input drift '+str(rec))
counts['frozen_inputs']=len(inputs)
tree=json.loads(read('sources/preprints-tree.json'));check(not tree['truncated'],'complete tree is truncated')
blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
m=json.loads((S/'source-manifest.json').read_text());check(m['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','pin changed')
for x in m['files']:
 b=read(x['local']);check(sha(b)==x['sha256'] and len(b)==x['bytes'],'pinned bytes '+x['path'])
 git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 check(git==x['git_blob']==blobs.get(x['path']),'pinned Git identity '+x['path'])
 check(x['url']=='https://raw.githubusercontent.com/openai/math/'+m['pin']+'/'+x['path'],'pinned URL '+x['path'])
counts['pinned_source_files']=len(m['files'])
primary=json.loads((S/'literature/manifest.json').read_text());failures=[];np=0
for x in primary:
 if 'error' in x:failures.append(x);continue
 b=read(x['path']);check(sha(b)==x['sha256'] and len(b)==x['bytes'],'primary bytes '+x['path']);np+=1
 if x['path'].endswith('.pdf'):check(b.startswith(b'%PDF-'),'not a PDF '+x['path'])
counts['primary_retrievals']=np
c=json.loads((S/'contracts.json').read_text())
for x in c['read_passages']:
 b=read(x['path']);check(sha(b)==x['file_sha256'],'read file hash '+x['path'])
 fragment=b''.join(b.splitlines(keepends=True)[x['start']-1:x['end']])
 check(sha(fragment)==x['sha256'],'passage hash '+x['path'])
counts['contracts']=len(c['contracts']);counts['read_passages']=len(c['read_passages'])
report=R/'frontier/iterations/i30-einstein-metric-stability.md'
for link in re.findall(r'\]\(([^)]+)\)',report.read_text()):
 if link.startswith(('http:','https:','#')):continue
 check((report.parent/link).exists(),'broken report link '+link)
# Core contract markers protect against accidental omission, not mathematical validity.
for marker in ['1/16','s=η²','Square-root volume','every measurable','negative','Tian–Wang','Route A','Route B']:
 check(marker in report.read_text(),'missing contract marker '+marker)
result=dict(status='PASS' if not errors else 'FAIL',counts=counts,errors=errors,shared_index_drift=drift,recorded_primary_fetch_failures=failures,scope='Integrity only; not an independent mathematical proof or significance verdict.')
(E/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
raise SystemExit(bool(errors))
