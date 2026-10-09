"""Offline I21 integrity and exact diagnostic reproduction; live drift is separate."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,importlib.util
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i21_signed_saxl_dominance';E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
load=lambda p:json.loads(p.read_text())
seal=load(S/'artifact-seal.json')
for p,h in seal['files'].items():
 assert p=='frontier/iterations/i21-signed-saxl-dominance.md' or p.startswith(('frontier/sources/i21_signed_saxl_dominance/','frontier/experiments/i21_signed_saxl_dominance/'))
 assert sha((R/p).read_bytes())==h,p
inputs=load(S/'inputs.json');drift=[]
for x in inputs:
 b=(S/'inputs'/x['path']).read_bytes();assert sha(b)==x['sha256'] and len(b)==x['bytes'],x['path']
 live=R/x['path']
 if not live.exists() or sha(live.read_bytes())!=x['sha256']:drift.append(dict(path=x['path'],frozen_sha256=x['sha256'],live_sha256=sha(live.read_bytes()) if live.exists() else None))
tree=load(S/'inputs/sources/preprints-tree.json');assert tree['truncated'] is False
assert len([x for x in tree['tree'] if x['type']=='tree' and x['path'].count('/')==1])==749
blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
pm=load(S/'pinned-manifest.json')
for x in pm:
 b=(S/'pinned'/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==blobs[x['path']]
 assert x['url']=='https://raw.githubusercontent.com/openai/math/'+seal['pin']+'/'+x['path']
contracts=load(S/'source-contracts.json')
for x in contracts:
 t=''.join((S/'pinned'/x['path']).read_text().splitlines(keepends=True)[x['start']-1:x['end']]);assert t==x['text'] and sha(t.encode())==x['sha256']
reads=load(S/'source-read-passages.json')
for x in reads:
 t=''.join((S/'pinned'/x['path']).read_text().splitlines(keepends=True)[x['start_line']-1:x['end_line']]);assert sha(t.encode())==x['sha256']
primary=load(S/'primary-contracts.json')
for x in primary:
 t=(S/x['file']).read_text()[x['start_offset']:x['end_offset']];assert t==x['text'] and sha(t.encode())==x['sha256']
for x in load(S/'primary-read-passages.json'):
 t=(S/x['file']).read_text()
 t=t[x['start_offset']:x['end_offset']] if 'start_offset' in x else ''.join(t.splitlines(keepends=True)[x['start_line']-1:x['end_line']])
 assert sha(t.encode())==x['sha256']
lit=load(S/'literature/manifest.json')
for x in lit:
 assert 'error' not in x,x
 b=(S/'literature'/x['file']).read_bytes();assert sha(b)==x['sha256'] and len(b)==x['bytes']
spec=importlib.util.spec_from_file_location('i21check',E/'check.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
r=mod.main();expected=load(E/'results.json');assert json.loads(json.dumps(r))==expected
cert=load(E/'dominance-m3-certificate.json');dom=r['dominance'][1]
assert cert==json.loads(json.dumps(mod.make_certificate(r)))
assert cert['class_correlations']==json.loads(json.dumps(dom['class_correlations']))
assert sum(x*y for x,y in zip(cert['hook_character'],cert['scaled_plus_correlations']))==0
# The initial I19 snapshots were independently verified in the read-only recheck.
old=load(S/'inputs/frontier/sources/i19_fresh_structural_discovery/inputs.json');old_drift=[]
for x in old:
 if x['path'] in ('frontier/README.md','frontier/TEN-FINDINGS.md'):
  live=R/x['path'];h=sha(live.read_bytes())
  if h!=x['sha256']:old_drift.append(dict(path=x['path'],i19_frozen_sha256=x['sha256'],current_sha256=h))
counts=dict(sealed_artifacts=len(seal['files']),frozen_inputs=len(inputs),pinned_files=len(pm),source_contracts=len(contracts),source_read_passages=len(reads),primary_contracts=len(primary),primary_retrievals=len(lit),joint_sector_multiplicities=4*len(r['joint_sectors']),constructed_map_constituent_ranks=2*sum(len(x['rows']) for x in r['dominance']),sign_intertwiner_gram_identities=sum(x['signed_intertwiner_gram_checks'] for x in r['dominance']),new_literal_projection_cases=len(r['wider']['projection_cases']))
out=dict(status='PASS: integrity and exact finite diagnostics; not independent mathematical/significance acceptance',counts=counts,live_shared_index_drift=[x for x in drift if x['path'] in ('frontier/README.md','frontier/TEN-FINDINGS.md')],other_live_input_drift=[x for x in drift if x['path'] not in ('frontier/README.md','frontier/TEN-FINDINGS.md')],shared_index_drift_since_i19=old_drift,diagnostics_reproduced=True)
(E/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
