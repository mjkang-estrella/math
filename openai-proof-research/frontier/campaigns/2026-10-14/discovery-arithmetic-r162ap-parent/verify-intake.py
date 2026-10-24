#!/usr/bin/env python3
"""Read-only r162ap authentication; no mathematical gate is assigned."""
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent;R=B/'fresh-arithmetic-discovery-r162ap'
H={'final':'d1b393b42947ff01a7593eb4d1311645efe6d5ef3c575b6469dc0dc465e21cfc','manifest':'b75532736c15c36c453dd46970e43854ac4ddbd48a5a92abbc56799ad6eec877','report':'b73aaa7ca869a51d972f521bee42ea61c3d0f80e4d65b4ed57e6e3834014b72b'}
def sha(a):return hashlib.sha256(a).hexdigest()
def snap(root):
 out={}
 for f in root.rglob('*'):
  assert not f.is_symlink()
  if f.is_file():
   a=f.read_bytes();out[f.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return out
def run(h,controls=False):
 cmd=[sys.executable,'-I','-B',str(R/'VERIFY.py'),'--root',str(R)]
 if controls:cmd+=['--controls-only']
 else:cmd+=['--final-sha',h['final'],'--manifest-sha',h['manifest'],'--report-sha',h['report']]
 z=subprocess.run(cmd,cwd=P,capture_output=True,text=True);return dict(exit=z.returncode,stdout=z.stdout,stderr=z.stderr)
before=json.loads((D/'private/intake/root-before.json').read_text());assert snap(R)==before
actual=run(H);assert actual['exit']==0,actual
m=json.loads((R/'private/MANIFEST.json').read_text());assert len(m['files'])==58
raw=(P/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
o=json.loads(raw);assert not o['truncated'];tree={x['path']:x for x in o['tree']}
local_tree=json.loads((R/'private/source-tree.json').read_text())
for x in local_tree:assert x==tree[x['path']]
bindings=[]
for x in json.loads((R/'private/source-access.json').read_text()):
 f=R/'private'/x['local'];a=f.read_bytes();g=hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()
 assert len(a)==x['bytes']==tree[x['path']]['size'] and sha(a)==x['sha256'] and g==x['git_blob']==tree[x['path']]['sha']
 assert x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
 bindings.append(dict(path=x['path'],local=x['local'],bytes=len(a),git_blob=g))
assert len(bindings)==19
lean=json.loads((R/'private/lean-113-access.json').read_text());a=(R/'private/lean-113.md').read_bytes();assert len(a)==lean['bytes'] and sha(a)==lean['sha256']
inputs=json.loads((D/'private/completed-direct-inputs.json').read_text())
for x in inputs:
 f=P/x['path'];a=f.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and f.stat().st_mode==x['mode']
controls=[]
for name,h,only,expected in [('copied-and-altered-tiny-controls',H,True,0),('wrong-final-anchor',{**H,'final':'0'*64},False,1),('wrong-manifest-anchor',{**H,'manifest':'0'*64},False,1)]:
 z=run(h,only);assert z['exit']==expected,(name,z);controls.append(dict(name=name,expected_exit=expected,**z))
assert snap(R)==before
out=dict(status='MATCH',anchors=H,payload=dict(files=len(m['files']),bytes=sum(x['bytes'] for x in m['files'].values())),whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,canonical_text_bindings=bindings,canonical_tree_entries=len(local_tree),canonical_directories=len(m['directories']),scoped_lean_pointer=dict(bytes=lean['bytes'],sha256=lean['sha256'],independent_git_blob_authentication=False,semantic_proof_reading=False),completed_direct_inputs_unchanged=len(inputs),actual_verifier=actual,controls=controls,no_mutation_recreated=True,artifact_check_only=True,parent_source_and_primary_proofs_reread=False)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','payload','whole_root_files','canonical_tree_entries','canonical_directories','completed_direct_inputs_unchanged','artifact_check_only']}))
