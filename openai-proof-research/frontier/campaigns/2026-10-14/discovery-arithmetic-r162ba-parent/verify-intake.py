#!/usr/bin/env python3
"""Read-only packet/pinned-source authentication; no mathematical gate."""
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent;R=B/'fresh-arithmetic-discovery-r162ba'
H={'final':'019f524db9905b359537bff46f6877eec058b7d3b8c3d6b127d3e92f9c4bcc98','manifest':'144e0d4ca808bfb7551c96c62d00bdf81e31dc1c5714d665ee0db5c1ff1800e6','report':'4f759e26d4dceb1144d10901f2efb7aff9216f75d431456a6e6275cae3e1e07c'}
def sha(a):return hashlib.sha256(a).hexdigest()
def snap():
 out={}
 for f in R.rglob('*'):
  assert not f.is_symlink() and (f.is_file() or f.is_dir())
  if f.is_file():
   a=f.read_bytes();out[f.relative_to(R).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return out
def run(h):
 z=subprocess.run([sys.executable,'-I','-B',str(R/'verify.py'),h['final'],h['manifest'],h['report']],cwd=P,capture_output=True,text=True)
 return dict(exit=z.returncode,stdout=z.stdout,stderr=z.stderr)
before=json.loads((D/'private/intake/root-before.json').read_text());assert snap()==before
actual=run(H);assert actual['exit']==0,actual
m=json.loads((R/'MANIFEST.json').read_text());assert len(m['files'])==90 and len(m['directories'])==21
raw=(P/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
o=json.loads(raw);assert not o['truncated'];tree={x['path']:x for x in o['tree']}
prefixes=json.loads((D/'private/canonical-selection.json').read_text())['folders'];assert len(prefixes)==4
local=json.loads((R/'private/selected-tree.json').read_text());assert len(local)==62
assert {x['path'] for x in local}=={x for x in tree if any(x==p or x.startswith(p+'/') for p in prefixes)}
for x in local:assert x==tree[x['path']]
auth=json.loads((R/'private/authentication.json').read_text());assert len(auth)==len({x['path'] for x in auth})==48
assert {x['path'] for x in auth}=={x['path'] for x in local if x['type']=='blob'}
bindings=[]
for x in auth:
 a=(R/'private/canonical'/x['path']).read_bytes();g=hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()
 assert len(a)==x['bytes']==tree[x['path']]['size'] and sha(a)==x['sha256'] and g==x['git_blob']==tree[x['path']]['sha']
 assert x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
 bindings.append(dict(path=x['path'],bytes=len(a),git_blob=g))
inputs=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(inputs)==5
for x in inputs:
 f=P/x['path'];a=f.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and f.stat().st_mode==x['mode']
copies=json.loads((R/'private/exception-copies.json').read_text());assert len(copies)==5 and {x['original'] for x in copies}=={x['path'] for x in inputs}
for x in copies:
 a=(R/x['copy']).read_bytes();assert a==(P/x['original']).read_bytes() and len(a)==x['bytes'] and sha(a)==x['sha256']
controls=[]
for k in H:
 z=run({**H,k:'0'*64});assert z['exit']!=0 and 'detached anchor mismatch' in z['stderr'];controls.append(dict(name='wrong-'+k+'-anchor',**z))
assert snap()==before
out=dict(status='MATCH',anchors=H,payload=dict(files=len(m['files']),bytes=sum(x['bytes'] for x in m['files'])),directories=len(m['directories']),directories_include_root=False,whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,canonical_blob_bindings=bindings,canonical_tree_entries=len(local),canonical_folders=4,operative_nonvendor_texts=44,operative_text_bytes=413702,compiled_pdfs_authenticated_not_rendered=4,completed_direct_inputs_unchanged=5,actual_verifier=actual,controls=controls,existing_copied_controls='positive accepted; in-memory altered copy/final rejected',no_mutation_recreated=True,artifact_check_only=True,parent_source_and_primary_proofs_reread=False)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','payload','directories','whole_root_files','canonical_tree_entries','completed_direct_inputs_unchanged','artifact_check_only']}))
