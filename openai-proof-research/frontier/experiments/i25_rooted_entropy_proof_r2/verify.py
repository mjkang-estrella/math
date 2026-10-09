"""Offline R2 provenance verifier. Mathematical validity is assessed in the report.
--seal creates this review's seal, never the author's seal. --reproduce runs ONLY
the independent R2 diagnostic in its own output directory with bytecode disabled.
"""
from pathlib import Path
import hashlib, json, os, subprocess, sys

R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i25_rooted_entropy_proof_r2'
E=R/'frontier/experiments/i25_rooted_entropy_proof_r2'
REPORT=R/'frontier/reviews/i25-rooted-entropy-proof-r2.md'
F=S/'frozen'
OLD='frontier/sources/i25_matching_entropy_improvement_resumed'
sha=lambda b:hashlib.sha256(b).hexdigest()
def load(p): return json.loads(p.read_text())
def relative(p): return str(p.relative_to(R))
def inventory():
    return sorted([REPORT]+[p for d in (S,E) for p in d.rglob('*')
                            if p.is_file() and p not in (S/'artifact-seal.json',S/'verification.json')],key=relative)
def metadata(p):
    b=p.read_bytes(); return {'path':relative(p),'bytes':len(b),'sha256':sha(b)}

if '--seal' in sys.argv:
    (S/'artifact-seal.json').write_text(json.dumps([metadata(p) for p in inventory()],indent=2)+'\n')
errors=[]; drift=[]; counts={}
def check(ok,detail):
    if not ok: errors.append(detail)
def matches(p,row):
    return p.is_file() and sha(p.read_bytes())==row['sha256']

seal=load(S/'artifact-seal.json')
check([r['path'] for r in seal]==[relative(p) for p in inventory()],'R2 inventory differs from seal')
for row in seal: check(matches(R/row['path'],row),'R2 seal: '+row['path'])
counts['review_sealed_artifacts']=len(seal)

inputs=load(S/'inputs.json')
for row in inputs:
    check(matches(R/row['snapshot'],row),'frozen input: '+row['path'])
    if not matches(R/row['path'],row):
        if row['mutable_external']: drift.append({'kind':'shared_or_parent_mutable_input','path':row['path']})
        else: check(False,'live immutable input changed: '+row['path'])
counts['frozen_inputs']=len(inputs)

pres=load(S/'preservation.json'); preserved=pres['files']
for row in preserved:
    if not matches(R/row['path'],row):
        if row['mutable_external']: drift.append({'kind':'parent_mutable_verification','path':row['path']})
        else: check(False,'preserved original/resumed bytes changed: '+row['path'])
current=sorted(relative(p) for d in pres['roots'] for p in (R/d).rglob('*') if p.is_file())
before=sorted(row['path'] for row in preserved)
check(current==before,'original/resumed file inventory changed')
counts['preserved_files']=len(preserved)
counts['original_files']=sum('/i25_matching_entropy_improvement/' in r['path'] for r in preserved)

authorseal=load(F/OLD/'artifact-seal.json')
for row in authorseal: check(matches(R/row['path'],row),'author artifact seal: '+row['path'])
counts['author_sealed_artifacts']=len(authorseal)
tree=load(F/'sources/preprints-tree.json')
check(not tree['truncated'],'preprint tree truncated')
blobs={row['path']:row['sha'] for row in tree['tree'] if row['type']=='blob'}
pin=load(F/OLD/'pinned-manifest.json')
for row in pin:
    b=(F/row['local_path']).read_bytes()
    git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    check(sha(b)==row['sha256'] and git==row['git_blob']==blobs.get(row['path']),'pinned identity: '+row['path'])
    check(row['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+row['path'],'unpinned URL')
counts['pinned_sources']=len(pin)
contracts=load(F/OLD/'source-contracts.json')
for row in contracts:
    text=(F/row['path']).read_text()[row['start']:row['end']]
    check(text==row['text'] and sha(text.encode())==row['sha256'],'author source contract: '+str(row['labels']))
counts['inherited_source_contracts']=len(contracts)
for name in ('read-passages.json','primary-passages.json'):
    rows=load(F/OLD/name)
    for row in rows:
        text=''.join((F/row['path']).read_text().splitlines(keepends=True)[row['start_line']-1:row['end_line']])
        check(text==row['text'] and sha(text.encode())==row['sha256'],'author passage: '+row['path'])
    counts['inherited_'+name.removesuffix('.json')]=len(rows)
reads=load(S/'read-contracts.json')
for row in reads:
    text=''.join((R/row['path']).read_text().splitlines(keepends=True)[row['start_line']-1:row['end_line']])
    check(text==row['text'] and sha(text.encode())==row['sha256'],'R2 read contract: '+row['path'])
counts['review_read_contracts']=len(reads)
literature=load(F/OLD/'literature/manifest.json')
for row in literature: check(matches(F/row['path'],row),'primary bytes: '+row['path'])
counts['inherited_primary_artifacts']=len(literature)

if '--reproduce' in sys.argv:
    before=sha((E/'results.json').read_bytes())
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    proc=subprocess.run([sys.executable,str(E/'diagnostics.py')],cwd=R,env=env,capture_output=True,text=True)
    check(proc.returncode==0,'R2 diagnostic failed: '+proc.stdout+proc.stderr)
    check(sha((E/'results.json').read_bytes())==before,'R2 diagnostic result was not byte-identical')
    counts['independent_diagnostic_byte_reproductions']=1

env=load(S/'environment.json'); idx=Path(env['index_path'])
now=sha(idx.read_bytes()) if idx.is_file() else None
index={'path':str(idx),'initial_sha256':env['index_sha256'],'live_sha256':now,'changed':now!=env['index_sha256']}
result={'status':'PASS' if not errors else 'FAIL','counts':counts,'errors':errors,
        'external_mutable_drift':drift,'git_index_drift':index,
        'scope':'Byte, source-identity, passage and finite-diagnostic audit; standalone mathematical verdict is the R2 report. No upstream truth audit or significance decision.'}
(S/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
sys.exit(bool(errors))
