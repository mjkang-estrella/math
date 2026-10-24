#!/usr/bin/env python3
"""Read-only archive authentication, not a mathematical review gate."""
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
R=B/'fresh-arithmetic-discovery-r162ao'
H={'final':'7600c548cbe3134851abcc205fccbc98ecf117c7f4cd7903f5d0de9bb8e20de0','manifest':'550400cd10ff76006c3d757543cd432a8bb60e6707b2739ff2adf91957cfa307','report':'92d9a2f7b21992c30878327461fca36a00ab487bae29b75d630c183e34a6bf4b'}
def sha(a):return hashlib.sha256(a).hexdigest()
def snap(root):
 out={}
 for f in root.rglob('*'):
  assert not f.is_symlink()
  if f.is_file():
   a=f.read_bytes();out[f.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return out
def run(root,h):
 cmd=[sys.executable,'-I','-B',str(R/'verify_packet.py'),'--root',str(root),'--final-sha256',h['final'],'--manifest-sha256',h['manifest'],'--report-sha256',h['report']]
 z=subprocess.run(cmd,cwd=P,capture_output=True,text=True)
 return dict(exit=z.returncode,stdout=z.stdout,stderr=z.stderr)
before=json.loads((D/'private/intake/root-before.json').read_text());assert snap(R)==before
actual=run(R,H);assert actual['exit']==0,actual
v=json.loads(actual['stdout']);assert v['files']==55
tree_raw=(P/'sources/preprints-tree.json').read_bytes()
assert sha(tree_raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree_obj=json.loads(tree_raw);assert tree_obj['truncated'] is False
tree={x['path']:x for x in tree_obj['tree']}
local_tree=json.loads((R/'private/source-tree.json').read_text())
for x in local_tree:assert x==tree[x['path']]
m=json.loads((R/'private/MANIFEST.json').read_text());bindings=[]
for x in json.loads((R/'private/source-access.json').read_text()):
 candidates=[z for z in m['files'] if z['sha256']==x['sha256']]
 assert candidates
 f=R/candidates[0]['path'];a=f.read_bytes();gitsha=hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()
 assert len(a)==x['bytes']==tree[x['path']]['size'] and sha(a)==x['sha256'] and gitsha==x['git_blob']==tree[x['path']]['sha']
 assert x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
 bindings.append(dict(path=x['path'],local=candidates[0]['path'],bytes=len(a),git_blob=gitsha))
assert len(bindings)==11
inputs=json.loads((D/'private/completed-direct-inputs.json').read_text())
for x in inputs:
 f=P/x['path'];a=f.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and f.stat().st_mode==x['mode']
controls=[]
original=R/'private/controls/original';tiny={k:sha((original/rel).read_bytes()) for k,rel in [('final','private/FINAL.md'),('manifest','private/MANIFEST.json'),('report','REPORT.md')]}
for name,sub,expected,hh in [('original','original',0,tiny),('copied-good','good',0,tiny),('copied-corruption','corrupt',1,tiny),('wrong-explicit-anchor','good',1,{**tiny,'final':'0'*64})]:
 z=run(R/'private/controls'/sub,hh);assert z['exit']==expected,(name,z)
 controls.append(dict(name=name,expected_exit=expected,**z))
assert snap(R)==before
out=dict(status='MATCH',anchors=H,payload=v,whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,canonical_text_bindings=bindings,canonical_tree_entries=len(local_tree),completed_direct_inputs_unchanged=len(inputs),controls=controls,no_mutation_recreated=True,artifact_check_only=True,parent_source_and_primary_proofs_reread=False)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','payload','whole_root_files','canonical_tree_entries','completed_direct_inputs_unchanged','artifact_check_only']}))
