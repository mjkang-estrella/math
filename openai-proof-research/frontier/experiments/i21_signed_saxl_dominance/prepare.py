"""Freeze only task dependencies, verify pins, search complete inventory/cache."""
from pathlib import Path
import hashlib,json,shutil,re,datetime
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i21_signed_saxl_dominance'
E=ROOT/'frontier/experiments/i21_signed_saxl_dominance'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 paths=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/i19-fresh-structural-discovery.md','frontier/iterations/i17-fresh-discovery.md','frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json','frontier/sources/i19_fresh_structural_discovery/artifact-seal.json','frontier/sources/i19_fresh_structural_discovery/pinned-manifest.json','frontier/sources/i19_fresh_structural_discovery/inputs.json','frontier/sources/i19_fresh_structural_discovery/theorem-contracts.json','frontier/sources/i19_fresh_structural_discovery/read-locators.json','frontier/sources/i19_fresh_structural_discovery/primary-contracts.json','frontier/sources/i19_fresh_structural_discovery/literature/manifest.json','frontier/experiments/i19_fresh_structural_discovery/check.py','frontier/experiments/i19_fresh_structural_discovery/results.json','frontier/sources/i19_fresh_structural_discovery/literature/bessenrodt-bowman.html','frontier/sources/i19_fresh_structural_discovery/literature/bb-current-abstract.html']
 inputs=[]
 for p in paths:
  b=(ROOT/p).read_bytes();dst=S/'inputs'/p
  if dst.exists():assert dst.read_bytes()==b or p in ['frontier/README.md','frontier/TEN-FINDINGS.md']
  else:dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
  inputs.append(dict(path=p,sha256=sha(dst.read_bytes()),bytes=dst.stat().st_size))
 write(S/'inputs.json',inputs)
 tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text());assert tree['truncated'] is False
 dirs=sorted(x['path'] for x in tree['tree'] if x['type']=='tree' and x['path'].count('/')==1)
 assert len(dirs)==749
 blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
 cm=json.loads((S/'inputs/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text()); assert len(cm['files'])==9340
 selected=[x for x in cm['files'] if any(q in x['path'] for q in ['A-Cyclic-Polytabloid-Proof-of-Saxls','Universal-Tensor-Squares-for-Symmetric'])]
 cache=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
 for x in selected:
  b=(cache/x['path']).read_bytes();assert sha(b)==x['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==blobs[x['path']]
  dst=S/'pinned'/x['path'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
 write(S/'pinned-manifest.json',selected)
 terms=['Saxl','symmetric square','alternating square','exterior square','sign intertwiner','dominance order','Kronecker','tensor square']
 hits=[]
 for x in cm['files']:
  txt=(cache/x['path']).read_text(errors='replace')
  matches=[]
  for k,line in enumerate(txt.splitlines(),1):
   found=[q for q in terms if q.lower() in line.lower()]
   if found:matches.append(dict(line=k,terms=found,text=line))
  if matches:hits.append(dict(path=x['path'],matches=matches))
 write(S/'corpus-search.json',dict(terms=terms,records_scanned=len(cm['files']),hits=hits))
 write(S/'inventory.json',dict(entry_count=len(tree['tree']),manuscript_count=len(dirs),manuscript_directories=dirs,selected_manuscripts=sorted({x['path'].split('/')[1] for x in selected}),title_matches=[p for p in dirs if re.search('Saxl|Kronecker|Tensor-Square|Symmetric-Group|Alternating-Group',p,re.I)],truncated=False))
 contracts=[]
 for x in selected:
  p=S/'pinned'/x['path'];text=p.read_text();lines=text.splitlines(keepends=True)
  for a,line in enumerate(lines):
   if re.search(r'\\begin\{(theorem|lemma|proposition|corollary)\}',line):
    env=re.search(r'\\begin\{(\w+)\}',line)[1];b=next((i for i in range(a,len(lines)) if '\\end{'+env+'}' in lines[i]),len(lines)-1)
    block=''.join(lines[a:b+1]);contracts.append(dict(path=x['path'],start=a+1,end=b+1,sha256=sha(block.encode()),text=block))
 write(S/'source-contracts.json',contracts)
 print(json.dumps(dict(frozen=len(inputs),pinned=len(selected),contracts=len(contracts),inventory=len(dirs),cache=len(cm['files']),matched_files=len(hits))))
if __name__=='__main__':main()
