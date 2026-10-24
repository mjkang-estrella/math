#!/usr/bin/env python3
"""Read-only authentication of the r162aq selection; not a mathematical gate."""
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent;R=B/'fresh-arithmetic-discovery-r162aq'
H={'final':'7201618f3569a3e4a45ed9f660b81e11b2e12e043b89f9cbbeb257cb4712ae59','manifest':'d1fe30b95b2c952fdf7882b5e058b39985e8a09e5293f0169fee99316c0ed5e7','report':'03effc7a4a57de41b77d1c79c2ec966d196698d0b487c1e7dfefef43ebadd410'}
def sha(a):return hashlib.sha256(a).hexdigest()
def snap(root):
 o={}
 for f in root.rglob('*'):
  assert not f.is_symlink()
  if f.is_file():
   a=f.read_bytes();o[f.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return o
def run(root,h):
 cmd=[sys.executable,'-I','-B',str(R/'verify.py'),'--root',str(root),'--manifest','MANIFEST.json','--final','private/FINAL.md','--report','REPORT.md','--final-sha256',h['final'],'--manifest-sha256',h['manifest'],'--report-sha256',h['report']]
 z=subprocess.run(cmd,cwd=P,capture_output=True,text=True);return dict(exit=z.returncode,stdout=z.stdout,stderr=z.stderr)
before=json.loads((D/'private/intake/root-before.json').read_text());assert snap(R)==before
actual=run(R,H);assert actual['exit']==0,actual
m=json.loads((R/'MANIFEST.json').read_text());assert len(m['files'])==76
assert set(before)=={x['path'] for x in m['files']}|{'MANIFEST.json','REPORT.md'}
raw=(P/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';obj=json.loads(raw);assert not obj['truncated'];tree={x['path']:x for x in obj['tree']}
tree_entries=0
for rel in ['private/selected-tree.json','private/companion-tree.json','private/exact-tables-tree.json']:
 entries=json.loads((R/rel).read_text())
 for x in entries:assert x==tree[x['path']]
 tree_entries+=len(entries)
bindings=[];scoped=[]
for rel in ['private/source-access.json','private/companion-access.json','private/exact-tables-access.json']:
 for x in json.loads((R/rel).read_text()):
  a=(R/'private'/x['local']).read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256']
  assert x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
  if x['path'].startswith('lean/'):
   assert x['path']=='lean/docs/114.md';scoped.append(dict(path=x['path'],bytes=len(a),independent_git_binding=False));continue
  g=hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest();assert g==x['git_blob']==tree[x['path']]['sha'] and len(a)==tree[x['path']]['size']
  bindings.append(dict(path=x['path'],local=x['local'],bytes=len(a),git_blob=g))
assert len(bindings)==37 and len(scoped)==1
inputs=json.loads((D/'private/completed-direct-inputs.json').read_text())
for x in inputs:
 f=P/x['path'];a=f.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and f.stat().st_mode==x['mode']
tiny=R/'controls/original';h={k:sha((tiny/v).read_bytes()) for k,v in [('final','private/FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]};controls=[]
for name,root,hh,expected in [('original',tiny,h,0),('copied-mutation',R/'controls/copied',h,1),('wrong-report-anchor',tiny,{**h,'report':'0'*64},1)]:
 z=run(root,hh);assert z['exit']==expected,(name,z);controls.append(dict(name=name,expected_exit=expected,**z))
assert snap(R)==before
out=dict(status='MATCH',anchors=H,payload=dict(files=len(m['files']),bytes=sum(x['bytes'] for x in m['files'])),whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,canonical_text_bindings=bindings,canonical_tree_entries=tree_entries,scoped_lean_pointer=scoped,completed_direct_inputs_unchanged=len(inputs),actual_verifier=actual,controls=controls,no_mutation_recreated=True,artifact_check_only=True,parent_source_and_primary_proofs_reread=False)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','payload','whole_root_files','canonical_tree_entries','completed_direct_inputs_unchanged','artifact_check_only']}))
