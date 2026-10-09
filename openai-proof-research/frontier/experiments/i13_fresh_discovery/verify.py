"""Offline integrity verification; does not modify shared inputs or reseal artifacts."""
import datetime,hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i13_fresh_discovery'
sha=lambda b:hashlib.sha256(b).hexdigest()
failures=[]
pinned=json.loads((OUT/'pinned-manifest.json').read_text())
for x in pinned:
 b=(ROOT/x['local_path']).read_bytes()
 if sha(b)!=x['sha256']:failures.append('pinned sha256 '+x['upstream_path'])
 if hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()!=x['git_blob']:failures.append('pinned Git blob '+x['upstream_path'])
literature=json.loads((OUT/'literature/manifest.json').read_text())
for x in literature:
 if 'error' in x:failures.append('retrieval '+x['id']);continue
 p=ROOT/x['path']
 if sha(p.read_bytes())!=x['sha256']:failures.append('literature PDF '+x['id'])
 if sha(p.with_suffix('.txt').read_bytes())!=x['text_sha256']:failures.append('literature text '+x['id'])
snaps=json.loads((OUT/'input-snapshots.json').read_text());changes=[]
for x in snaps:
 if sha((ROOT/x['snapshot']).read_bytes())!=x['sha256']:failures.append('snapshot '+x['path'])
 now=sha((ROOT/x['path']).read_bytes())
 if now!=x['sha256']:changes.append({'path':x['path'],'initial_sha256':x['sha256'],'current_sha256':now,'note':'Concurrent shared-input change; snapshot preserved. This agent did not write this path.'})
tree=json.loads((OUT/'inputs/sources/preprints-tree.json').read_text());assert len(tree['tree'])==13223 and tree['truncated'] is False
catalog={x['path']:x for x in tree['tree']}
for x in pinned:
 if catalog[x['upstream_path']]['sha']!=x['git_blob']:failures.append('tree membership '+x['upstream_path'])
manifest=json.loads((OUT/'artifact-manifest.json').read_text())
for x in manifest['artifacts']:
 p=ROOT/x['path']
 if not p.exists() or sha(p.read_bytes())!=x['sha256']:failures.append('artifact '+x['path'])
excluded={OUT/'artifact-manifest.json',OUT/'verification.json'}
actual={str(p.relative_to(ROOT)) for base in [OUT,ROOT/'frontier/experiments/i13_fresh_discovery'] for p in base.rglob('*') if p.is_file() and p not in excluded}
actual.add('frontier/iterations/i13-fresh-discovery.md')
if actual!={x['path'] for x in manifest['artifacts']}:failures.append('artifact path-set changed')
result={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pinned_sources':len(pinned),'primary_pdfs':len(literature),'snapshots':len(snaps),'artifacts':len(manifest['artifacts']),'complete_tree_entries':len(tree['tree']),'truncated':False,'snapshot_bytes_unchanged':True,'concurrent_input_changes':changes,'artifact_manifest_sha256':sha((OUT/'artifact-manifest.json').read_bytes()),'failures':failures,'status':'PASS' if not failures else 'FAIL','limits':'Integrity and deterministic diagnostics only. No independent proof/contribution review or certification.'}
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));assert not failures
