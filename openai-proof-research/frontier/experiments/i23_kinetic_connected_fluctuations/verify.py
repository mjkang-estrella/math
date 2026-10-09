"""Verify frozen provenance and assigned artifacts; never repair shared inputs."""
from pathlib import Path
import hashlib,json,re,sys
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i23_kinetic_connected_fluctuations';E=Path(__file__).resolve().parent
REPORT=ROOT/'frontier/iterations/i23-kinetic-connected-fluctuations.md'
sha=lambda b:hashlib.sha256(b).hexdigest()
def assigned_files():
 return sorted([REPORT]+[p for base in (S,E) for p in base.rglob('*') if p.is_file() and p not in [S/'artifact-seal.json',E/'verification.json'] and '__pycache__' not in p.parts])
if '--seal' in sys.argv:
 (S/'artifact-seal.json').write_text(json.dumps({'scope':'Assigned I23 report and source/experiment trees only; integrity does not establish mathematical validity.','files':[dict(path=str(p.relative_to(ROOT)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in assigned_files()]},indent=2)+'\n')
seal=json.loads((S/'artifact-seal.json').read_text());actual={str(p.relative_to(ROOT)) for p in assigned_files()};expected={x['path'] for x in seal['files']};assert actual==expected,(actual-expected,expected-actual)
for x in seal['files']:
 b=(ROOT/x['path']).read_bytes();assert sha(b)==x['sha256'] and len(b)==x['bytes'],x['path']
inputs=json.loads((S/'input-manifest.json').read_text());drift=[]
for x in inputs:
 b=(S/'inputs'/x['path']).read_bytes();assert sha(b)==x['sha256'] and len(b)==x['bytes'],x['path']
 live=ROOT/x['path']
 if not live.exists() or sha(live.read_bytes())!=x['sha256']:drift.append(dict(path=x['path'],shared_index=x['shared'],frozen_sha256=x['sha256'],live_sha256=sha(live.read_bytes()) if live.exists() else None))
index=json.loads((S/'inputs/sources/preprints-tree.json').read_text());assert not index.get('truncated',False);tree={x['path']:x for x in index['tree']};pin=json.loads((S/'pinned-manifest.json').read_text());assert pin['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
for x in pin['files']:
 b=(S/'corpus'/x['path']).read_bytes();assert sha(b)==x['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==tree[x['path']]['sha'];assert '/'+pin['pin']+'/' in x['url']
statements=json.loads((S/'statement-contracts.json').read_text())['contracts']
for x in statements:
 t=(S/'corpus'/x['path']).read_text();assert x['text'] in t and sha(x['text'].encode())==x['sha256'];assert t[:t.index(x['text'])].count('\n')+1==x['start_line']
passages=json.loads((S/'reading-contracts.json').read_text())['passages']
for x in passages:
 lines=(S/x['path']).read_text().splitlines();t='\n'.join(lines[x['start_line']-1:x['end_line']])+'\n';assert t==x['text'] and sha(t.encode())==x['sha256'],x['path']
lit=json.loads((S/'literature/manifest.json').read_text())
for x in lit:
 if 'file' in x:
  b=(ROOT/x['file']).read_bytes();assert sha(b)==x['sha256'] and len(b)==x['bytes'],x['file']
# Check each pinned PDF's extracted version header, rather than silently promoting a current URL to a pin.
versions={'lebihan':'2408.03597v2','pss':'1301.2514v2','bgss':'2008.10403v2','cluster':'2205.04110v1','bgss_equilibrium':'2201.04514v1','lebihan_hard_v1':'2212.04392v1'}
for name,v in versions.items():assert v in (S/'literature'/f'{name}.txt').read_text()[:10000],v
# All local report links must resolve inside this project.
for target in re.findall(r'\]\(([^)]+)\)',REPORT.read_text()):
 if not target.startswith(('http://','https://')):assert (REPORT.parent/target.split('#')[0]).resolve().exists(),target
out=dict(status='PASS',artifacts=len(seal['files']),pinned_files=len(pin['files']),frozen_inputs=len(inputs),statement_contracts=len(statements),read_passages=len(passages),literature_retrievals=len(lit),pinned_primary_versions=len(versions),live_input_drift=drift,nonshared_live_input_drift=[x for x in drift if not x['shared_index']],limitation='Integrity and finite contracts only; not independent analytic proof or significance acceptance.')
(E/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
