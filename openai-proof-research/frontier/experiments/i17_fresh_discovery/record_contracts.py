"""Record exact pinned statement blocks and explicitly read source ranges."""
from pathlib import Path
import json,re,hashlib
BASE=Path(__file__).resolve().parents[3];OUT=BASE/'frontier/sources/i17_fresh_discovery'
manifest=json.loads((OUT/'pinned-manifest.json').read_text());blocks=[]
for item in manifest:
 p=BASE/item['local']
 if p.suffix!='.tex':continue
 s=p.read_text();pattern=r'\\begin\{(theorem|proposition|lemma|corollary)\}(.*?)\\end\{\1\}'
 for m in re.finditer(pattern,s,re.S):
  labels=re.findall(r'\\label\{([^}]+)\}',m.group(0))
  if not labels:continue
  start=s[:m.start()].count('\n')+1;end=s[:m.end()].count('\n')+1
  blocks.append(dict(path=item['path'],local=item['local'],git_blob=item['git_blob'],labels=labels,start_line=start,end_line=end,exact_statement=m.group(0),statement_sha256=hashlib.sha256(m.group(0).encode()).hexdigest()))
(OUT/'theorem-contracts.json').write_text(json.dumps(blocks,indent=2)+'\n')
# Only read passages are listed here; saved blocks elsewhere are not blanket read claims.
ranges={
 'A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026':{'01-introduction.tex':[(1,None)],'02-tensors.tex':[(1,210)],'06-groups.tex':[(295,None)],'07-consequences.tex':[(1,None)]},
 'Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026':{'introduction.tex':[(1,None)]},
 'A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026':{'introduction.tex':[(1,None)],'dominance.tex':[(1,78)],'band-quotient.tex':[(1,None)],'completion.tex':[(1,None)]},
 'Subset-Sum-in-Time-2-power-0-49n-October-4-2026':{'introduction.tex':[(1,None)],'checksum.tex':[(1,150),(470,None)]},
 'A-Low-Space-Algorithm-for-Worst-Case-Subset-Sum-September-26-2026':{'introduction.tex':[(1,None)]},
 'The-low-temperature-Sherrington-Kirkpatrick-free-energy-limiting-law-September-24-2026':{'01-introduction.tex':[(1,None)],'consequences.tex':[(1,None)],'04-reduction.tex':[(1,100),(240,413)]},
 'The-low-temperature-Sherrington-Kirkpatrick-fluctuation-scale-September-24-2026':{'companion-interface.tex':[(1,190),(260,None)]}}
records=[]
for item in manifest:
 p=Path(item['path']);root=p.parts[1];name=p.name
 if root not in ranges or name not in ranges[root]:continue
 lines=(BASE/item['local']).read_text().splitlines(keepends=True)
 for start,end in ranges[root][name]:
  end=len(lines) if end is None else min(end,len(lines));s=''.join(lines[start-1:end])
  records.append(dict(local=item['local'],git_blob=item['git_blob'],start_line=start,end_line=end,range_sha256=hashlib.sha256(s.encode()).hexdigest(),scope='Selected actual statement/proof passage read; upstream claims accepted, not audited.'))
(OUT/'read-ranges.json').write_text(json.dumps(records,indent=2)+'\n')
print(len(blocks),'labelled statement blocks;',len(records),'selected read ranges')
