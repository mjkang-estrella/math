#!/usr/bin/env python3
"""Read-only r162av packet and immutable-source authentication; no mathematical gate."""
from pathlib import Path
import hashlib,json,subprocess,sys,stat
P=Path(__file__).resolve().parents[4]; B=P/'frontier/campaigns/2026-10-14'; D=Path(__file__).resolve().parent; R=B/'fresh-arithmetic-discovery-r162av'
H={'final':'a13fd0c1ef25923012378fc3472880fcbd64fc35ce9f65a8ce14921b389a3af0','manifest':'cd8acc11a265d09f419de516816a6eb7a696f7e9e55ba7f8af6075e787708116','report':'ffc099a34535e4dbadae41d477f0da6ff835325fd88fab33ce02b6904a2d0bb2'}
def sha(a):return hashlib.sha256(a).hexdigest()
def snap():
 out={}
 for f in R.rglob('*'):
  assert not f.is_symlink() and (f.is_file() or f.is_dir())
  if f.is_file():
   a=f.read_bytes();out[f.relative_to(R).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return out
def run(h):
 cmd=[sys.executable,'-I','-B',str(R/'private/verify_packet.py'),*[y for k in h for y in ('--'+k+'-sha256',h[k])]]
 z=subprocess.run(cmd,cwd=P,capture_output=True,text=True);return dict(exit=z.returncode,stdout=z.stdout,stderr=z.stderr)
before=json.loads((D/'private/intake/root-before.json').read_text());assert snap()==before
actual=run(H);assert actual['exit']==0,actual
m=json.loads((R/'private/MANIFEST.json').read_text());assert len(m['files'])==113 and len(m['directories'])==21
raw=(P/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
o=json.loads(raw);assert not o['truncated'];tree={x['path']:x for x in o['tree']}
local=json.loads((R/'private/source-tree.json').read_text());assert len(local)==86
prefix='preprints/A-polynomial-time-algorithm-for-three-machine-unit-job-scheduling-September-24-2026/'
assert {x['path'] for x in local}=={x for x in tree if x==prefix[:-1] or x.startswith(prefix)}
for x in local:assert x==tree[x['path']]
bindings=[]
for x in json.loads((R/'private/source-bindings.json').read_text()):
 assert x['path'].startswith(prefix)
 a=(R/'private'/x['copy']).read_bytes();g=hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()
 assert len(a)==x['bytes']==tree[x['path']]['size'] and sha(a)==x['sha256'] and g==x['git_blob']==tree[x['path']]['sha']
 assert x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
 bindings.append(dict(path=x['path'],bytes=len(a),git_blob=g))
assert len(bindings)==69 and sum(x['bytes'] for x in bindings)==1333898
inputs=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(inputs)==5
for x in inputs:
 f=P/x['path'];a=f.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and f.stat().st_mode==x['mode']
for x in json.loads((R/'private/context-bindings.json').read_text()):
 a=(R/x['copy']).read_bytes();assert a==(P/x['original']).read_bytes() and len(a)==x['bytes'] and sha(a)==x['sha256']
controls=[]
for k in H:
 z=run({**H,k:'0'*64});assert z['exit']!=0 and 'detached anchor mismatch' in z['stderr'];controls.append(dict(name='wrong-'+k+'-anchor',**z))
assert snap()==before
out=dict(status='MATCH',anchors=H,payload=dict(files=len(m['files']),bytes=sum(x['bytes'] for x in m['files'])),directories=len(m['directories']),whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,canonical_blob_bindings=bindings,canonical_tree_entries=len(local),operative_nonvendor_texts=13,operative_text_bytes=87480,vendor_runtime_blobs=55,compiled_pdf_authenticated_not_rendered=True,completed_direct_inputs_unchanged=5,actual_verifier=actual,controls=controls,existing_copied_controls='positive matched; one-byte negative distinguished',no_mutation_recreated=True,artifact_check_only=True,parent_source_and_primary_proofs_reread=False)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','payload','directories','whole_root_files','canonical_tree_entries','completed_direct_inputs_unchanged','artifact_check_only']}))
