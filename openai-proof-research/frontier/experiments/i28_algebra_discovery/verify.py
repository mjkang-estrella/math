"""Verify artifact integrity, pinned Git identities, and deterministic replay.

No network and no source/cache/index writes. Only diagnostics.json (exact replay)
and verification.json are written. Shared TEN-FINDINGS drift is separate.
"""
from pathlib import Path
import datetime, hashlib, json, subprocess, sys
ROOT=Path(__file__).resolve().parents[3]
S=Path('frontier/sources/i28_algebra_discovery')
E=Path('frontier/experiments/i28_algebra_discovery')
REPORT=Path('frontier/iterations/i28-algebra-discovery.md')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b): return hashlib.sha256(b).hexdigest()
def gitblob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p): return (ROOT/p).read_bytes()
def js(p): return json.loads(read(p))
errors=[]; drift=[]; counts={}
def check(ok, message):
 if not ok: errors.append(message)
seal=js(S/'artifact-manifest.json')
excluded={str(S/'artifact-manifest.json'),str(E/'verification.json')}
check(set(seal['excluded'])==excluded,'Unexpected exclusions')
check(seal['pin']==PIN,'Seal pin mismatch')
expected={e['path']:e for e in seal['files']}
actual={str(REPORT)}
for d in (S,E): actual.update(str(p.relative_to(ROOT)) for p in (ROOT/d).rglob('*') if p.is_file())
actual-=excluded
check(actual==set(expected),'Artifact set differs: '+repr(sorted(actual^set(expected))))
for p,e in expected.items():
 check(p in actual,'Missing artifact '+p)
 if p not in actual: continue
 b=read(p);check(len(b)==e['bytes'] and sha(b)==e['sha256'],'Artifact hash/length '+p)
counts['sealed_files']=len(expected)
for e in js(S/'input-manifest.json')['files']:
 frozen=read(S/'inputs'/e['path'])
 check(len(frozen)==e['bytes'] and sha(frozen)==e['sha256'],'Frozen dependency '+e['path'])
 live=ROOT/e['path']; livehash=sha(live.read_bytes()) if live.is_file() else None
 if livehash!=e['sha256']:
  row={'path':e['path'],'frozen_sha256':e['sha256'],'live_sha256':livehash}
  if e['path']=='frontier/TEN-FINDINGS.md': drift.append(row)
  else: errors.append('Immutable/live dependency changed: '+e['path'])
upstream=js(S/'inputs/sources/upstream.json')
check(upstream['commit']==PIN,'Frozen upstream pin')
tree=js(S/'inputs/sources/preprints-tree.json');entries={e['path']:e for e in tree['tree']}
check(not tree['truncated'],'Truncated source tree')
manuscripts=sum(e['type']=='tree' and e['path'].count('/')==1 for e in tree['tree'])
check(manuscripts==749,'Manuscript inventory count')
manifest=js(S/'inputs/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
cache={e['path']:e for e in manifest['files']}
check(len(cache)==9340 and manifest['pin']==PIN,'Cache count/pin')
for path,e in cache.items():
 p=Path('frontier/sources/i14_spectral_width_novelty_r3/corpus')/path
 try:b=read(p)
 except FileNotFoundError: errors.append('Missing cache '+path);continue
 check(len(b)==e['bytes'] and sha(b)==e['sha256'] and gitblob(b)==e['git_blob'],'Cache bytes '+path)
 check(entries[path]['sha']==e['git_blob'],'Tree/cache Git identity '+path)
selected=js(S/'pinned-manifest.json')
check(selected['pin']==PIN,'Selected pin')
for e in selected['files']:
 b=read(S/'pinned'/e['path'])
 check(len(b)==e['bytes'] and sha(b)==e['sha256'] and gitblob(b)==e['git_blob'],'Selected bytes '+e['path'])
 check(e==cache[e['path']],'Selected metadata differs from cache '+e['path'])
 check('/'+PIN+'/' in e['url'],'Unpinned source URL '+e['path'])
for e in js(S/'read-passages.json')['passages']:
 lines=read(e['path']).splitlines(keepends=True)
 check(sha(b''.join(lines[e['start_line']-1:e['end_line']]))==e['sha256'],'Read passage '+e['path'])
contracts=js(S/'source-contracts.json')['contracts']
for e in contracts:
 b=read(e['path']); lines=b.splitlines(keepends=True)
 check(sha(b)==e['source_sha256'] and gitblob(b)==e['git_blob'],'Contract source '+e['path'])
 check(sha(b''.join(lines[e['start_line']-1:e['end_line']]))==e['passage_sha256'],'Contract passage '+e['path'])
 check(e['exact_statement'] in b.decode(),'Contract exact statement '+e['path'])
for name in ('manifest.json','additional-manifest.json','lubotzky-salomon-manifest.json'):
 for e in js(S/'literature'/name):
  b=read(e['path']);check(len(b)==e['bytes'] and sha(b)==e['sha256'],'Literature '+e['path'])
e=js(S/'literature/loring-v4-manifest.json'); b=read(S/'literature'/e['file'])
check(len(b)==e['bytes'] and sha(b)==e['sha256'],'Loring v4 bytes')
for e in js(S/'version-history.json'):
 check(sha(read(e['path']))==e['source_sha256'],'Version history source '+e['path'])
counts.update(manuscripts=manuscripts,cache_files=len(cache),selected_sources=len(selected['files']),exact_contracts=len(contracts))
replay={'status':'NOT RUN: prior integrity failure'}
if not errors:
 p=subprocess.run([sys.executable,str(ROOT/E/'diagnostics.py')],cwd=ROOT,capture_output=True,text=True)
 check(p.returncode==0,'Diagnostics replay failed: '+p.stderr)
 digest=sha(read(E/'diagnostics.json'))
 check(digest==expected[str(E/'diagnostics.json')]['sha256'],'Diagnostics output is not deterministic')
 replay={'exit_code':p.returncode,'stdout':p.stdout,'output_sha256':digest}
result={'status':'PASS' if not errors else 'FAIL','verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'artifact_manifest_sha256':sha(read(S/'artifact-manifest.json')),'counts':counts,
 'errors':errors,'shared_index_drift':drift,'diagnostics_replay':replay,
 'limits':'Integrity and bounded exact diagnostics, not independent proof review or significance acceptance. No source truth audit.'}
(ROOT/E/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2));sys.exit(bool(errors))
