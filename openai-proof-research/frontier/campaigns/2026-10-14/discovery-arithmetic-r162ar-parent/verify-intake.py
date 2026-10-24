#!/usr/bin/env python3
"""Read-only r162ar authentication; no mathematical gate."""
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent;R=B/'fresh-arithmetic-discovery-r162ar'
H={'final':'c8e1c81161d7b52d77fa6f3159951b8e1037729e962356fffdbdc2f369facfe5','manifest':'24e32665ed9f82c8a4de4a545cc54b8374a7269bdbc6fe1349f6562295d3a197','report':'05b3131bda4b21793ae240fcb018ca1575c2af801a3df3ecf637f91cc21b6d97'}
def sha(a):return hashlib.sha256(a).hexdigest()
def snap(root):
 out={}
 for f in root.rglob('*'):
  assert not f.is_symlink()
  if f.is_file():
   a=f.read_bytes();out[f.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return out
def run(h):
 cmd=[sys.executable,'-I','-B',str(R/'verify.py'),'--root',str(R),'--final-sha',h['final'],'--manifest-sha',h['manifest'],'--report-sha',h['report']]
 z=subprocess.run(cmd,cwd=P,capture_output=True,text=True);return dict(exit=z.returncode,stdout=z.stdout,stderr=z.stderr)
before=json.loads((D/'private/intake/root-before.json').read_text());assert snap(R)==before
actual=run(H);assert actual['exit']==0,actual
m=json.loads((R/'MANIFEST.json').read_text());assert len(m['files'])==55
raw=(P/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';o=json.loads(raw);assert not o['truncated'];tree={x['path']:x for x in o['tree']}
local=json.loads((R/'private/source-tree.json').read_text())
for x in local:assert x==tree[x['path']]
bindings=[]
for x in json.loads((R/'private/authentication.json').read_text()):
 a=(R/'private/canonical'/x['path']).read_bytes();g=hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest();assert len(a)==x['bytes']==tree[x['path']]['size'] and sha(a)==x['sha256'] and g==x['git_blob']==tree[x['path']]['sha']
 assert x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'];bindings.append(dict(path=x['path'],bytes=len(a),git_blob=g))
assert len(bindings)==27
lean=json.loads((R/'private/lean116-access.json').read_text());a=(R/'private/lean116.md').read_bytes();assert len(a)==lean['bytes'] and sha(a)==lean['sha256']
inputs=json.loads((D/'private/completed-direct-inputs.json').read_text())
for x in inputs:
 f=P/x['path'];a=f.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and f.stat().st_mode==x['mode']
controls=[]
for name,h in [('wrong-final-anchor',{**H,'final':'0'*64}),('wrong-report-anchor',{**H,'report':'0'*64})]:
 z=run(h);assert z['exit']!=0;controls.append(dict(name=name,expected_nonzero=True,**z))
assert snap(R)==before
out=dict(status='MATCH',anchors=H,payload=dict(files=len(m['files']),bytes=sum(x['bytes'] for x in m['files'])),whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,canonical_text_bindings=bindings,canonical_tree_entries=len(local),scoped_lean_pointer=dict(bytes=len(a),independent_git_binding=False),completed_direct_inputs_unchanged=len(inputs),actual_verifier=actual,controls=controls,no_mutation_recreated=True,artifact_check_only=True,parent_source_and_primary_proofs_reread=False)
out['scoped_lean_pointer']['bytes']=lean['bytes']
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','payload','whole_root_files','canonical_tree_entries','completed_direct_inputs_unchanged','artifact_check_only']}))
