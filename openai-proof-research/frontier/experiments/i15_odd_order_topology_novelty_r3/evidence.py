"""Reconstruct R3 evidence from read-only inputs; no writes outside the R3 directories."""
from pathlib import Path
import json,hashlib,shutil,re,html,subprocess
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i15_odd_order_topology_novelty_r3';C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(name,x):(S/name).write_text(json.dumps(x,indent=2)+'\n')
inputs=json.loads((S/'input-manifest.json').read_text())
for x in inputs:
 assert sha((R/x['path']).read_bytes())==sha((R/x['snapshot']).read_bytes())==x['sha256'],x['path']
for path in ['frontier/sources/i15_odd_order_topology/pinned-manifest.json']:
 b=(R/path).read_bytes();p=S/'inputs'/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 if path not in {x['path'] for x in inputs}:inputs.append({'path':path,'snapshot':str(p.relative_to(R)),'bytes':len(b),'sha256':sha(b)})
write('input-manifest.json',inputs)
pinned=json.loads((R/'frontier/sources/i15_odd_order_topology/pinned-manifest.json').read_text())
for x in pinned:
 b=(R/x['snapshot']).read_bytes();assert len(b)==x['bytes'];assert sha(b)==x['sha256'];assert b==(C/x['path']).read_bytes();assert PIN in x['url']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob_sha1']
contracts=json.loads((R/'frontier/sources/i15_odd_order_topology_r2/source-contracts.json').read_text())
for x in contracts:
 b=(C/x['path']).read_bytes();assert sha(b)==x['source_sha256'];t='\n'.join(b.decode().splitlines()[x['start_line']-1:x['end_line']]);assert t==x['statement'];assert sha(t.encode())==x['statement_sha256']
passages=json.loads((R/'frontier/sources/i15_odd_order_topology_r2/source-proof-passages.json').read_text())
for x in passages:
 b=(C/x['path']).read_bytes();assert sha(b)==x['source_sha256'];t='\n'.join(b.decode().splitlines()[x['start_line']-1:x['end_line']]);assert t==x['text'];assert sha(t.encode())==x['text_sha256']
# A complete immutable local copy of every source file used by the inherited contracts.
source_index=[]
for path in sorted({x['path'] for x in contracts}|{x['path'] for x in passages}):
 b=(C/path).read_bytes();p=S/'upstream'/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 source_index.append({'path':path,'snapshot':str(p.relative_to(R)),'sha256':sha(b),'bytes':len(b),'url':f'https://raw.githubusercontent.com/openai/math/{PIN}/{path}'})
write('upstream-manifest.json',source_index)
# This is a conservative record of passages personally read in R3, not a claim to reread every paper.
B='preprints/Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026/build/'
MT='preprints/A-marked-tensor-obstruction-to-four-dimensional-disk-embedding-September-24-2026/build/'
PD='preprints/A-PD4-group-without-an-aspherical-manifold-model-September-24-2026/build/'
BO='preprints/A-boundary-only-obstruction-to-four-dimensional-disk-embedding-September-24-2026/build/'
spec=[(B+'sections/chambers.tex',1,792,'Full marked-body proof, chamber module, chosen caps and positive filling'),(B+'sections/formal.tex',1,827,'Full cut/formal interface; actual ideal, algebraicity, recentering, nilpotent correction'),(B+'sections/tensors.tex',1,150,'Arbitrary-graph and arbitrary-law assignment, binary specialization'),(B+'sections/reflection.tex',1,253,'Full chamber/reflection input, manifold implication, finite covers'),(B+'sections/cyclic.tex',1,166,'Full cyclic nonrepresentability criterion and height mechanism'),(B+'sections/introduction.tex',1,100,'Actual main results'),(MT+'sections/01-geometry.tex',245,345,'Primitive-annulus replacement and marked three-tip body'),(MT+'sections/01-geometry.tex',435,555,'Contraction, sheet pairing and framing'),(MT+'sections/04-algebraicity.tex',1,100,'Full critical scheme and based holonomy'),(MT+'sections/00-introduction.tex',40,105,'Actual marked disk theorem'),(PD+'paper.tex',1,135,'Actual finite PD4 nonmodel result'),(PD+'sections/chamber.tex',1,275,'Three-tip model, side marking, cofiber'),(BO+'sections/introduction.tex',1,95,'Actual boundary-only theorem'),(BO+'sections/geometry.tex',135,335,'Ribbon framing and finite staged collar placement')]
read=[]
for path,a,z,purpose in spec:
 p=C/path
 if not p.exists():
  # Avoid guessing section names; resolve by the exact filename in the full tree.
  matches=list((C/('/'.join(path.split('/')[:2]))).rglob(Path(path).name));assert len(matches)==1,(path,matches);p=matches[0];path=str(p.relative_to(C))
 b=p.read_bytes();lines=b.decode().splitlines();assert len(lines)>=z,(path,len(lines),z);t='\n'.join(lines[a-1:z]);read.append({'path':path,'url':f'https://raw.githubusercontent.com/openai/math/{PIN}/{path}','source_sha256':sha(b),'start_line':a,'end_line':z,'text_sha256':sha(t.encode()),'purpose':purpose,'text':t})
write('r3-source-read-passages.json',read)
# Primary theorem passages: line numbers refer to Python splitlines() of the retained pdftotext -layout output.
ranges={
'bartels-lueck':[(1,80),(138,161)],'elementary-amenable-four':[(1,140)],'dovermann-schultz':[(1,57)],'bak-morimoto':[(1,124)],'arabadji-baykur-v3':[(1,65)],'davis-leary':[(1,145)],'avramidi-okun-schreve':[(335,368)],'davis-book':[(11112,11205),(11855,11950)],'davis-exotic':[(645,676)],'krushkal-quinn':[(140,179)],'allender-boolean':[(163,230)],'block-weinberger':[(25,170),(180,390)],'davis-lueck':[(208,266)],'hilman-kirstein-kremer':[(1,140)],'kremer-2026-v1':[(1,190)],'pesikoff-v1':[(1,115),(790,822)],'kremer-borel-v1':[(1,190)],'kang-park-taniguchi-published':[(1,122)],'lee-cyclic':[(1,45),(140,171)],'conner-raymond':[(393,418),(1910,2080)],'raymond-scott-publisher':[(1,98),(228,288),(386,425)],'block-weinberger-center':[(1,110)],'dhhrs-current-v3':[(1,180)],'khan-connected-sums':[(170,277)],'hadziosmanovic-mangioni':[(40,155)]}
ret=[]
for f in ['retrieval-manifest.json','extra-retrieval-manifest.json','supplement-retrieval-manifest.json']:ret+=json.loads((S/f).read_text())
lookup={x['name']:x for x in ret};lit=[]
for name,rr in ranges.items():
 x=lookup[name];b=(R/x['path']).read_bytes();assert sha(b)==x['sha256'];p=(R/x['path']).with_suffix('.txt');b2=p.read_bytes();lines=b2.decode().splitlines()
 rec={'name':name,'url':x['url'],'pdf_path':x['path'],'pdf_sha256':sha(b),'text_path':str(p.relative_to(R)),'text_sha256':sha(b2),'passages':[]}
 for a,z in rr:
  assert len(lines)>=z,(name,len(lines),z);t='\n'.join(lines[a-1:z]);rec['passages'].append({'start_line':a,'end_line':z,'sha256':sha(t.encode()),'text':t})
 if name=='block-weinberger-center':rec['display_title']='Cappell–Weinberger–Yan, Closed Aspherical Manifolds with Center (filename is a retrieval job key, not authorship)'
 lit.append(rec)
write('primary-read-passages.json',lit)
versions=[]
for p in sorted((S/'literature').glob('metadata-*.html')):
 t=p.read_text();m=re.search(r'<div class="submission-history">(.*?)</div>',t,re.S);assert m
 hist=re.sub(r'\s+',' ',html.unescape(re.sub('<[^>]+>',' ',m.group(1)))).strip();v=max(map(int,re.findall(r'\[v(\d+)\]',hist)))
 versions.append({'arxiv_id':p.stem.removeprefix('metadata-'),'latest_version_at_retrieval':v,'history':hist,'metadata_path':str(p.relative_to(R)),'sha256':sha(p.read_bytes())})
write('current-versions.json',versions)
assert lookup['kremer-2026-current']['sha256']==lookup['kremer-2026-v1']['sha256'];assert lookup['kremer-borel-current']['sha256']==lookup['kremer-borel-v1']['sha256']
result={'pinned_files_verified':len(pinned),'contracts_verified':len(contracts),'inherited_proof_passages_verified':len(passages),'source_files_copied':len(source_index),'r3_source_read_passages':len(read),'primary_works_with_fresh_read_passages':len(lit),'fresh_retained_22_equal_prior':all(x.get('equals_prior') for x in ret if 'prior_sha256' in x),'current_kremer_pdfs_equal_v1':True,'input_snapshots_verified':len(inputs)}
write('evidence-audit.json',result);print(json.dumps(result,indent=2))
