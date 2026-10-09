#!/usr/bin/env python3
"""Read-only verification of dependencies; writes only R2 results/contracts."""
from pathlib import Path
import hashlib, json, re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i15_odd_order_topology_r2'
OLD=ROOT/'frontier/sources/i15_odd_order_topology'
RES=ROOT/'frontier/sources/i15_odd_order_topology_resumed'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b): return hashlib.sha256(b).hexdigest()
def read(p): return json.loads(p.read_text())
def verify(rec, base=ROOT):
 p=base/rec['path']; b=p.read_bytes()
 assert len(b)==rec['bytes'] and sha(b)==rec['sha256'], str(p)
def output(name,obj): (S/name).write_text(json.dumps(obj,indent=2)+'\n')
deps=read(S/'dependency-manifest.json')
for r in deps:
 verify(r)
 assert (ROOT/r['path']).read_bytes()==(ROOT/r['snapshot']).read_bytes(),r['path']
tree=read(ROOT/'sources/preprints-tree.json'); assert tree['truncated'] is False
entries={r['path']:r for r in tree['tree']}; assert len(entries)==len(tree['tree'])
pinned=read(OLD/'pinned-manifest.json')
for r in pinned:
 b=(ROOT/r['snapshot']).read_bytes()
 assert sha(b)==r['sha256'] and len(b)==r['bytes']
 assert r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==entries[r['path']]['sha']==r['git_blob_sha1']
contracts=read(OLD/'contracts.json')
for r in contracts:
 p=OLD/'upstream'/r['path']; b=p.read_bytes()
 t='\n'.join(b.decode().splitlines()[r['start_line']-1:r['end_line']])
 assert sha(b)==r['source_sha256'] and t==r['statement'] and sha(t.encode())==r['statement_sha256']
 for label in r['labels']: assert '\\label{'+label+'}' in t
assert read(RES/'contracts.json')==contracts
seal=read(RES/'artifact-manifest.json')
for key in ['files','old_dependencies']:
 for r in seal[key]: verify(r)
retrievals=0
for f in ['retrieval-manifest.json','additional-retrieval-manifest.json','final-retrieval-manifest.json']:
 for r in read(RES/f):
  if 'sha256' not in r: continue
  verify(r,RES); retrievals+=1
  if 'text_path' in r: assert sha((RES/r['text_path']).read_bytes())==r['text_sha256']
readings=read(RES/'reading-index.json')['records']; passages=0
for r in readings:
 assert sha((ROOT/r['text_path']).read_bytes())==r['text_sha256']
 assert sha((ROOT/r['pdf_path']).read_bytes())==r['pdf_sha256']
 lines=(ROOT/r['text_path']).read_text().splitlines()
 for q in r['passages']:
  t='\n'.join(lines[q['start_line']-1:q['end_line']]); assert t==q['text']; passages+=1
# Independently retain the complete actual statement inventory and bounded proof passages.
output('source-contracts.json',contracts)
paths={r['path'] for r in contracts}
passage_specs=[
 ('B','Nonhomeomorphic-closed*','sections/chambers.tex',1,792,'Complete changed-body, exterior, middle-module and filling comparison'),
 ('B','Nonhomeomorphic-closed*','sections/formal.tex',1,827,'Complete cut, mixed-endpoint, actual-law-ideal and correction comparison'),
 ('B','Nonhomeomorphic-closed*','sections/reflection.tex',1,253,'Exact reflection contract and full/reused-label cover comparison'),
 ('B','Nonhomeomorphic-closed*','sections/cyclic.tex',1,166,'Exact cyclic criterion and complete height proof'),
 ('B','Nonhomeomorphic-closed*','sections/tensors.tex',1,150,'Actual arbitrary-loopless-graph assignment statement and scope'),
 ('B','Nonhomeomorphic-closed*','sections/introduction.tex',1,100,'Main theorem statements and scope'),
 ('MT','A-marked-tensor*','sections/01-geometry.tex',1,570,'Marked annuli, relative placement, normal frames and cancellation'),
 ('MT','A-marked-tensor*','sections/03-edge-germs.tex',365,506,'Based Artinian slice and torus-identity gauge; edge potential'),
 ('MT','A-marked-tensor*','sections/04-algebraicity.tex',1,100,'Full critical-scheme algebraicity statement and geometric input'),
 ('MT','A-marked-tensor*','sections/04a-formal-comparison.tex',1,70,'Full formal trace comparison contract'),
 ('MT','A-marked-tensor*','sections/05-vertices.tex',420,470,'Fixed-list correction hypotheses'),
 ('MT','A-marked-tensor*','sections/05-vertices.tex',550,810,'Recentered actual product ideals and full-parameter correction'),
 ('MT','A-marked-tensor*','sections/00-introduction.tex',40,105,'Main disk theorem scope'),
 ('PD','A-PD4-group*','paper.tex',1,135,'Actual main theorem and dimension/category'),
 ('PD','A-PD4-group*','sections/chamber.tex',1,498,'Side marking, full middle duality and topological cuts'),
 ('BO','A-boundary-only*','sections/introduction.tex',1,95,'Actual boundary-only theorem scope'),
 ('BO','A-boundary-only*','sections/geometry.tex',135,335,'Independent ribbon framing and stage construction comparison'),
]
passages_out=[]
for code,pat,rel,start,end,purpose in passage_specs:
 p=next((OLD/'upstream/preprints').glob(pat))/'build'/rel
 b=p.read_bytes(); lines=b.decode().splitlines(); assert end<=len(lines)
 t='\n'.join(lines[start-1:end]); up=str(p.relative_to(OLD/'upstream'))
 passages_out.append(dict(source=code,path=up,url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+up,start_line=start,end_line=end,source_sha256=sha(b),text_sha256=sha(t.encode()),purpose=purpose,text=t))
output('source-proof-passages.json',passages_out)
report=ROOT/'frontier/reviews/i15-odd-order-topology-r2.md'
local_links=[]
if report.exists():
 for target in re.findall(r'\]\(([^)]+)\)',report.read_text()):
  if '://' in target: continue
  assert (report.parent/target).exists(),target
  local_links.append(target)
result=dict(report_local_links=len(local_links),status='PASS: identities and exact excerpts; not a proof verdict',pin=PIN,dependencies=len(deps),pinned_files=len(pinned),source_contracts=len(contracts),resumed_sealed_files=len(seal['files']),old_sealed_dependencies=len(seal['old_dependencies']),tree_entries=len(entries),tree_blobs=sum(r['type']=='blob' for r in entries.values()),successful_resumed_retrievals=retrievals,primary_text_records=len(readings),primary_exact_passages=passages,source_proof_passages=len(passages_out),network_used=False,original_or_resumed_writes=False)
output('audit-results.json',result); print(json.dumps(result,indent=2))
