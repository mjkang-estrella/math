"""Integrity and source-label checks only; not an asymptotic proof checker."""
import pathlib,hashlib,json,re
R=pathlib.Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i07_analysis'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((S/'retrieval-manifest.json').read_text())
up=[]
for e in m['sources']:
 b=(R/e['local']).read_bytes()
 up.append(dict(path=e['path'],sha256_ok=hashlib.sha256(b).hexdigest()==e['sha256'],git_blob_ok=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['expected_blob']))
ll=json.loads((S/'literature-manifest.json').read_text())['sources']
lit=[dict(name=e['name'],sha256_ok=sha(R/e['local'])==e['sha256']) for e in ll if e['status']=='retrieved']
contracts=[
 ('BE-high','Strong-diffeomorphic-approximation-in-three-dimensions-for-p-gt-2-September-24-2026/build/sections/01-introduction.tex',['main:theorem','ha:approximation']),
 ('BE-low','Strong-diffeomorphic-approximation-in-three-dimensions-for-1-le-p-le-2-September-24-2026/build/sections/01-introduction.tex',['main:theorem']),
 ('MTW-foundation','Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/build/sections/introduction.tex',['thm:main','thm:foundation']),
 ('MTW-Holder','Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/build/sections/introduction.tex',['thm:main']),
 ('CD-rough','Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/build/paper.tex',['thm:main','cor:localized']),
 ('CD-smooth-plus','Determination-of-a-metric-and-a-unitary-connection-from-one-boundary-patch-October-5-2026/build/sections/01-introduction.tex',['thm:main']),
 ('Brenier-stability','Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/build/source/sections/introduction.tex',['main:stability'])]
labels=[]
for name,p,ls in contracts:
 f=S/'upstream'/p; lines=f.read_text().splitlines()
 for label in ls:
  found=[i+1 for i,s in enumerate(lines) if '\\label{'+label+'}' in s]
  labels.append(dict(contract=name,path=str(f.relative_to(R)),label=label,lines=found,sha256=sha(f)))
inputs=json.loads((S/'input-snapshot.json').read_text())
input_checks=[dict(path=p,unchanged=sha(R/p)==v) for p,v in inputs.items()]
out=dict(scope='Integrity and exact source-label checks, not proof or novelty validation',upstream_count=len(up),upstream=up,literature=lit,labels=labels,inputs=input_checks)
out['all_source_checks_pass']=all(x['sha256_ok'] and x['git_blob_ok'] for x in up) and all(x['sha256_ok'] for x in lit) and all(x['lines'] for x in labels)
(S/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
files=[R/'frontier/iterations/i07-analysis.md']+list(S.rglob('*'))+list((R/'frontier/experiments/i07_analysis').rglob('*'))
hashes={str(f.relative_to(R)):sha(f) for f in sorted(files) if f.is_file() and f.name!='artifact-hashes.json'}
(S/'artifact-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
print(json.dumps(dict(source_checks_pass=out['all_source_checks_pass'],pinned_sources=len(up),external_retrievals=len(lit),source_labels=len(labels),artifact_hashes=len(hashes),changed_inputs=[x['path'] for x in input_checks if not x['unchanged']]),indent=2))
