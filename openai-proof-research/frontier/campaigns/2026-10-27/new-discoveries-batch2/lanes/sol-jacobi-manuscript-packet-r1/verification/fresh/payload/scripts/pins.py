#!/usr/bin/env python3
"""Assert the installed toolchain and every manifest dependency, without fetching."""
import hashlib,json,subprocess
from pathlib import Path
BASE=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def git(p,*args):return subprocess.check_output(['git','-C',str(p),*args],stderr=subprocess.PIPE,text=True).strip()
def check(base=BASE):
 p=json.loads((base/'pins.json').read_text()); manifest=base/'provenance/lake-manifest.json'
 assert sha(manifest)==p['lake_manifest_sha256']
 assert sha(p['lean_binary'])==p['lean_sha256']
 assert subprocess.check_output([p['lean_binary'],'--version'],text=True).strip()==p['lean_version']
 assert sha(base/'formal/run_lean.py')==p['runner_sha256']
 assert sha(p['authoritative_lake_manifest'])==p['lake_manifest_sha256']
 rows=json.loads(manifest.read_text())['packages']; assert len(rows)==9
 packages=Path(p['packages_root']); available=sorted(x.name for x in packages.iterdir() if (x/'.lake/build/lib/lean').is_dir()); assert set(available)<=set(x['name'] for x in rows); assert 'mathlib' in available
 result=[]
 for row in rows:
  path=packages/row['name']; rev=git(path,'rev-parse','HEAD'); assert rev==row['rev'],row['name']
  # Tracked working tree AND index must be clean; untracked build caches are expected.
  status=git(path,'status','--porcelain=v1','--untracked-files=no'); assert not status,(row['name'],'tracked changes')
  result.append({'name':row['name'],'revision':rev,'tracked_tree_and_index_clean':True,'library_path':str(path/'.lake/build/lib/lean'),'runner_includes_library_path':row['name'] in available})
 return {'lean_sha256':p['lean_sha256'],'lean_version':p['lean_version'],'runner_sha256':p['runner_sha256'],'lake_manifest_sha256':p['lake_manifest_sha256'],'packages':result,'untracked_build_caches':'not source revisions; not shipped'}
if __name__=='__main__':print(json.dumps(check(),indent=2))
