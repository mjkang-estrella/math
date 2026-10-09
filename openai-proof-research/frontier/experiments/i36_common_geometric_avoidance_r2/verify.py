"""Offline R2 provenance and exact-diagnostic verification; not formal proof."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
sys.dont_write_bytecode = True
from reproduce_author import reproduce

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i36_common_geometric_avoidance_r2'
X=Path(__file__).resolve().parent
REPORT=ROOT/'frontier/reviews/i36-common-geometric-avoidance-r2.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text())

def check(row,path='path',hashkey='sha256'):
    b=(ROOT/row[path]).read_bytes()
    assert sha(b)==row[hashkey], ('hash mismatch',row[path])
    if 'bytes' in row: assert len(b)==row['bytes']
    return b

seal=read(S/'artifact-seal.json')
assert seal['pin']==PIN
for row in seal['files']: check(row)
excluded={S/'artifact-seal.json',X/'verification.json'}
actual={str(p.relative_to(ROOT)) for folder in (S,X) for p in folder.rglob('*')
        if p.is_file() and p not in excluded and '__pycache__' not in p.parts}
actual.add(str(REPORT.relative_to(ROOT)))
assert actual=={r['path'] for r in seal['files']}, 'Unsealed/missing owned artifact'

shared=[]; generated=[]; inputs=read(S/'input-manifest.json')
for row in inputs:
    p=ROOT/row['path']; now=sha(p.read_bytes()) if p.exists() else None
    if now!=row['sha256']:
        assert row['mutable'], ('immutable input drift',row['path'])
        item={'path':row['path'],'baseline':row['sha256'],'current':now}
        (shared if row['path'] in ['frontier/TEN-FINDINGS.md','frontier/iterations/README.md'] else generated).append(item)
    frozen=S/'frozen'/row['path']
    if frozen.exists(): assert sha(frozen.read_bytes())==row['sha256']

brief_source=S/'frozen/frontier/iterations/iteration36-common-geometric-avoidance-proof-r2-task.json'
assert (S/'full-brief.txt').read_text()==read(brief_source)['brief']
assert sha(REPORT.read_bytes())==seal['report_sha256']

tree=read(ROOT/'sources/preprints-tree.json')
assert tree['truncated'] is False
entries={r['path']:r for r in tree['tree']}
pinned=read(S/'pinned-manifest.json')
for row in pinned:
    b=check(row,'local'); blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert blob==row['git_blob']==entries[row['path']]['sha']
    assert row['url']==f'https://raw.githubusercontent.com/openai/math/{PIN}/'+row['path']
for row in read(S/'read-passages.json'):
    b=''.join((ROOT/row['path']).read_text().splitlines(keepends=True)[row['first_line']-1:row['last_line']]).encode()
    assert sha(b)==row['sha256']
for row in read(S/'source-contracts.json'):
    p=ROOT/row['path']; assert sha(p.read_bytes())==row['source_sha256']
    block='\n'.join(p.read_text().splitlines()[row['first_line']-1:row['last_line']])
    assert row['text'] in block and sha(row['text'].encode())==row['sha256']
for row in read(S/'primary-retrievals.json'):
    if 'path' in row: check(row)

run=subprocess.run([sys.executable,'-B',str(X/'checks.py')],capture_output=True,check=True)
assert run.stdout==(X/'checks.json').read_bytes(), 'R2 diagnostic output mismatch'
checks=json.loads(run.stdout)
assert checks['status']=='PASS'
author=reproduce(); recorded=read(X/'author-reproduction.json')
for obj in (author,recorded):
    obj['result'].pop('mutable_shared_ledger_drift',None)
assert author==recorded, 'Author verifier changed except permitted ledger drift'
result={'status':'PASS','scope':'Evidence integrity and exact finite diagnostics; written proof verdict in R2 review.',
        'original_proof_verdict':'PASS without repairs','pin':PIN,
        'sealed_owned_files':len(seal['files']),'bound_inputs':len(inputs),'pinned_files':len(pinned),
        'read_passages':len(read(S/'read-passages.json')),'contracts':len(read(S/'source-contracts.json')),
        'independent_diagnostics':checks,'author_reproduction':'PASS; unchanged source executed with sole report write intercepted',
        'shared_ledger_drift_since_r2_start':shared,'generated_report_drift_since_r2_start':generated,
        'author_shared_ledger_drift':read(X/'author-reproduction.json')['result']['mutable_shared_ledger_drift']}
output=json.dumps(result,indent=2,sort_keys=True)+'\n'
(X/'verification.json').write_text(output)
print(output,end='')
