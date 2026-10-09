#!/usr/bin/env python3
"""Independent retained-byte verifier. Mathematical verdict lives in the report."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3]
E=Path(__file__).resolve().parent
S=R/'frontier/sources/i30_einstein_metric_stability_r2'
A=R/'frontier/sources/i30_einstein_metric_stability'
errors=[];drift=[];counts={}
sha=lambda b:hashlib.sha256(b).hexdigest()
def check(ok,msg):
    if not ok:errors.append(msg)
def checkrow(x,p):
    try:b=p.read_bytes()
    except OSError as ex:errors.append(str(ex));return
    check(len(b)==x['bytes'] and sha(b)==x['sha256'],'Bytes changed: '+str(p.relative_to(R)))
inputs=json.loads((S/'input-manifest.json').read_text())['files']
for x in inputs:
    checkrow(x,R/x['frozen'])
    if (R/x['path']).exists():
        live=sha((R/x['path']).read_bytes())
        if live!=x['sha256']:
            if x.get('shared'):drift.append(dict(path=x['path'],frozen_sha256=x['sha256'],live_sha256=live))
            else:errors.append('Nonshared review input drift: '+x['path'])
    else:errors.append('Missing live input '+x['path'])
counts['frozen_inputs']=len(inputs)
deps=json.loads((S/'dependency-manifest.json').read_text())['files']
for x in deps:checkrow(x,R/x['path'])
counts['read_only_dependencies']=len(deps)

tree=json.loads((R/'sources/preprints-tree.json').read_text())
check(tree['truncated'] is False,'Tree must not be truncated')
blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
pin=json.loads((A/'source-manifest.json').read_text());check(pin['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','Corpus pin changed')
for x in pin['files']:
    b=(R/x['local']).read_bytes();checkrow(x,R/x['local'])
    git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    check(git==x['git_blob']==blobs[x['path']],'Git blob identity '+x['path'])
    check(x['url']=='https://raw.githubusercontent.com/openai/math/'+pin['pin']+'/'+x['path'],'Raw pin URL '+x['path'])
counts['pinned_source_files']=len(pin['files'])

passages=json.loads((S/'read-passages.json').read_text())['passages']
for x in passages:
    b=(R/x['path']).read_bytes();frag=b''.join(b.splitlines(keepends=True)[x['start']-1:x['end']])
    check(sha(b)==x['file_sha256'],'Read source changed '+x['path'])
    check(sha(frag)==x['sha256'],'Read passage changed '+x['path'])
    check((R/x['retained']).read_bytes()==frag,'Retained passage mismatch '+x['retained'])
counts['read_passages']=len(passages)

primary=json.loads((A/'literature/manifest.json').read_text());failures=[];n=0
for x in primary:
    if 'error' in x:failures.append(x);continue
    checkrow(x,R/x['path']);n+=1
counts['reused_primary_retrievals']=n
new=json.loads((S/'new-primary-manifest.json').read_text())['retrievals']
for x in new:
    if 'error' in x:failures.append(x);continue
    checkrow(x,R/x['path']);check(x['status']==200,'Metadata status')
counts['new_metadata_retrievals']=sum('path' in x for x in new)

contracts=json.loads((S/'contracts.json').read_text())
check(contracts['verdict']=='PASS' and contracts['repair_required'] is False,'Wrong review disposition')
counts['review_contracts']=len(contracts['contracts'])
report=R/'frontier/reviews/i30-einstein-metric-stability-r2.md'
for link in re.findall(r'\]\(([^)]+)\)',report.read_text()):
    if not link.startswith(('http:','https:','#')):check((report.parent/link).exists(),'Broken report link '+link)

repro=json.loads((E/'author-reproduction.json').read_text());check(repro['status']=='PASS','Author reproduction failed')
for command in repro['commands']:
    check(command['returncode']==0 and command['result']['status']=='PASS','Author command failed')
    check(sha((R/command['script']).read_bytes())==command['sha256'],'Author code changed after reproduction')
drift.extend(repro['commands'][1]['result']['shared_index_drift'])
check(repro['commands'][0]['result']['total_exact_cases']==20698,'Author diagnostic count')
check(repro['commands'][2]['result']['sealed_artifacts']==57,'Author seal count')
own=json.loads((E/'diagnostics.json').read_text());check(own['status']=='PASS' and own['total_exact_cases']==4759,'Independent diagnostics')
counts['independent_exact_cases']=own['total_exact_cases']

out=dict(status='PASS' if not errors else 'FAIL',counts=counts,errors=errors,shared_ledger_drift=drift,recorded_fetch_failures=failures,scope='Integrity and recorded diagnostics; not an automated proof certification.')
(E/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
raise SystemExit(bool(errors))
