#!/usr/bin/env python3
"""Independent frozen-record authentication. Copyright 2026 Myeongjin Kang; MIT."""
from pathlib import Path
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]; BASE=HERE.parent; A=BASE/'kn-minus-edge-formal-v1'
def digest(b): return hashlib.sha256(b).hexdigest()
def row(p):
 b=p.read_bytes();return {'path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':digest(b)}
def check(p,r):
 b=p.read_bytes(); assert len(b)==r['bytes'] and digest(b)==r['sha256'],str(p)
 return row(p)
report={'formal_payload':[],'formal_fixed_inputs':[],'original_source_mappings':[]}
out=json.loads((A/'output-manifest.json').read_text())
for r in out['files']:report['formal_payload'].append(check(A/r['path'],r))
visible={str(p.relative_to(A)) for p in A.rglob('*') if p.is_file() and not any(part.startswith('.') or part=='__pycache__' for part in p.relative_to(A).parts)}
listed={r['path'] for r in out['files']}|{'output-manifest.json'}
report['unlisted_visible_payload']=sorted(visible-listed); report['listed_missing']=sorted(listed-visible)
assert not report['unlisted_visible_payload'] and not report['listed_missing']
inp=json.loads((A/'input-manifest.json').read_text()); exceptions=[]
for r in inp['files']:
 if r.get('verification')=='historical_mutable_context':
  assert r['path']=='frontier/NEW-TEN-2026-10-14.md';exceptions.append(r)
 else:report['formal_fixed_inputs'].append(check(ROOT/r['path'],r))
assert len(exceptions)==1
historical=subprocess.check_output(['git','show','ecb3ab7a:./frontier/NEW-TEN-2026-10-14.md'],cwd=ROOT)
r=exceptions[0]; assert len(historical)==r['bytes'] and digest(historical)==r['sha256']
snapshot=BASE/'kn-minus-edge-parent/formal-r1-input-campaign.md'
assert snapshot.read_bytes()==historical
report['historical_context']={'original':r,'git_revision':'ecb3ab7a','parent_snapshot':row(snapshot),'current':row(ROOT/r['path']),'scope':'only campaign progress ledger; no Lean/build/math source exemption'}
# Original source-records mappings independently checked, rather than trusting the author audit.
for package,mf,root in [('fresh-substantial-discovery-r2','input-manifest.json',BASE/'fresh-substantial-discovery-r2'),('fresh-substantial-discovery-r2','output-manifest.json',BASE/'fresh-substantial-discovery-r2'),('kn-minus-edge-proof-r1','output-manifest.json',ROOT),('kn-minus-edge-contribution-r1','outputs.json',BASE/'kn-minus-edge-contribution-r1')]:
 rs=json.loads((BASE/package/mf).read_text())['files']; records=[check(root/r['path'],r) for r in rs]
 report['original_source_mappings'].append({'manifest':row(BASE/package/mf),'count':len(records),'records':records})
tex=BASE/'fresh-substantial-discovery-r2/sources/upstream/kn/main.tex'
blob=hashlib.sha1(b'blob '+str(tex.stat().st_size).encode()+b'\0'+tex.read_bytes()).hexdigest()
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text())
# GitHub tree shape may be list/dict. Match exact immutable blob.
entries=tree.get('tree',[]) if isinstance(tree,dict) else tree
matches=[x for x in entries if x.get('sha')==blob]
assert any(x['path'].endswith('The-crossing-number-of-complete-graphs-September-23-2026/build/main.tex') for x in matches),matches
report['upstream_blob']={'sha1':blob,'matching_tree_entries':matches,'file':row(tex),'truth_stipulated':True}
# All review's immediate input references, including manifests themselves.
paths=[ROOT/'AGENTS.md',ROOT/'sources/upstream.json',ROOT/'sources/preprints-tree.json']+list(A.glob('*'))
paths += [BASE/'fresh-substantial-discovery-r2'/s for s in ['candidate.md','source-contracts.md','README.md','provenance.json']]
paths += [BASE/'kn-minus-edge-proof-r1'/s for s in ['review.md','provenance.json','input-manifest.json','output-manifest.json']]
paths += [BASE/'kn-minus-edge-contribution-r1'/s for s in ['review.md','sources.md','input-hashes.json','outputs.json']]
paths += [BASE/'kn-minus-edge-parent'/s for s in ['proof-r1-disposition.json','contribution-r1-disposition.json','proof-r1-verification.json','contribution-r1-verification.json','formal-r1-input-campaign.md']]
records={str(p):row(p) for p in paths if p.is_file()}
(HERE/'input-manifest.json').write_text(json.dumps({'root':str(ROOT),'files':sorted(records.values(),key=lambda x:x['path']),'note':'Read extents are in provenance.json; byte authentication is not mathematical reading.'},indent=2)+'\n')
report['status']='PASS'
(HERE/'authentication.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS',len(report['formal_payload']),'formal payload,',len(report['formal_fixed_inputs']),'fixed inputs, one original historical ledger recovered, source mappings 24+9+19+5; exact upstream blob')
