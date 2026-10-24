#!/usr/bin/env python3
"""Read-only r162at authentication; no mathematical gate."""
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent;R=B/'fresh-arithmetic-discovery-r162at'
H={'final':'579c36ec75797a6a3ff209363cff27cb88d68a24c828237085af80681b23f1cd','manifest':'21b1c633ec4d1d8c486d6426cd29d3016ca3d6aa472f5d832bd4b2a2354420fa','report':'80ed126e5a003aa1a0edb59590093b357441087093bc76b87c71e79dc40afd03'}
def sha(a):return hashlib.sha256(a).hexdigest()
def snap(root):
 out={}
 for f in root.rglob('*'):
  assert not f.is_symlink()
  if f.is_file():
   a=f.read_bytes();out[f.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return out
def run(h):
 cmd=[sys.executable,'-I','-B',str(R/'verify_packet.py'),'--root',str(R),'--final-sha256',h['final'],'--manifest-sha256',h['manifest'],'--report-sha256',h['report']]
 z=subprocess.run(cmd,cwd=P,capture_output=True,text=True);return dict(exit=z.returncode,stdout=z.stdout,stderr=z.stderr)
before=json.loads((D/'private/intake/root-before.json').read_text());assert snap(R)==before
actual=run(H);assert actual['exit']==0,actual
m=json.loads((R/'private/MANIFEST.json').read_text());assert len(m['files'])==49
raw=(P/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';o=json.loads(raw);assert not o['truncated'];tree={x['path']:x for x in o['tree']}
local=json.loads((R/'private/selected-tree.json').read_text())
for x in local:assert x==tree[x['path']]
bindings=[]
for x in json.loads((R/'private/authentication.json').read_text()):
 a=(P/x['local']).read_bytes();g=hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest();assert len(a)==x['bytes']==tree[x['path']]['size'] and sha(a)==x['sha256'] and g==x['git_blob']==tree[x['path']]['sha']
 assert x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'];bindings.append(dict(path=x['path'],bytes=len(a),git_blob=g))
assert len(bindings)==17
inputs=json.loads((D/'private/completed-direct-inputs.json').read_text())
for x in inputs:
 f=P/x['path'];a=f.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and f.stat().st_mode==x['mode']
controls=[]
for name,h in [('wrong-final-anchor',{**H,'final':'0'*64}),('wrong-report-anchor',{**H,'report':'0'*64})]:
 z=run(h);assert z['exit']!=0;controls.append(dict(name=name,expected_nonzero=True,**z))
assert snap(R)==before
out=dict(status='MATCH',anchors=H,payload=dict(files=len(m['files']),bytes=sum(x['bytes'] for x in m['files'])),whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,canonical_text_bindings=bindings,canonical_tree_entries=len(local),scoped_lean_pointer=None,completed_direct_inputs_unchanged=len(inputs),actual_verifier=actual,controls=controls,no_mutation_recreated=True,artifact_check_only=True,parent_source_and_primary_proofs_reread=False)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','payload','whole_root_files','canonical_tree_entries','completed_direct_inputs_unchanged','artifact_check_only']}))
