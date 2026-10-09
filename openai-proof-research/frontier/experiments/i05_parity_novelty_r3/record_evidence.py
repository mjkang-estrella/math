import json,hashlib,re,datetime
from pathlib import Path
R=Path.cwd();O=R/'frontier/sources/i05_parity_novelty_r3'
def sha(b):return hashlib.sha256(b).hexdigest()
inputs=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/iterations/README.md','frontier/iterations/i05-parity-pd.md','frontier/reviews/i05-parity-pd-r2.md','frontier/findings/R006-progression-PD-primitive-root-density.md','frontier/findings/R008-parity-PD-independence.md']
(O/'input-snapshot.json').write_text(json.dumps([{'path':p,'sha256':sha((R/p).read_bytes()),'bytes':(R/p).stat().st_size} for p in inputs],indent=2))
labels={'thm:q-affine','thm:elliott','cor:affine','q:progression','q:rough-shifts','q:center','q:testing','prop:analytic-centering','thm:mrt','prop:affine-progression','sh:sign','sh:core','sh:discrepancy','sh:correlation','sh:small-square-error','thm:main','thm:two-sided','cor:sparse-bound','cor:constant-high','lp:prime-polynomial','lp:log-phase','cor:transference-pairing','lem:marked-coefficient-transfer','det:cauchy-square','thm:hecke-zero-free','thm:density','cor:separable-products','cor:ostmann','thm:smooth'}
ranges=[]
for p in sorted((O/'upstream').rglob('*.tex')):
 lines=p.read_text().splitlines(keepends=True)
 for i,line in enumerate(lines):
  for label in re.findall(r'\\label\{([^}]+)\}',line):
   if label in labels:
    lo=max(0,i-8);hi=min(len(lines),i+40);b=''.join(lines[lo:hi]).encode()
    ranges.append({'path':str(p.relative_to(O)),'label':label,'label_line':i+1,'range_start':lo+1,'range_end':hi,'range_sha256':sha(b),'file_sha256':sha(p.read_bytes())})
(O/'source-locators.json').write_text(json.dumps(ranges,indent=2))
# Explicit PDF page extracts retain form-feed-based physical page numbers.
selection={'carella-v3':[1,4,6,18,19,20],'carella-v2':[4,20,21],'moree-v1':[20,21],'lichtman-v2':[1,2,3],'lt-published':[2,3,4],'wang-v1':[2,3,4],'tt-siegel-published':[3,4,5],'pintz-v1':[2],'shao-published':[3]}
ex=[]
for name,ns in selection.items():
 pages=(O/(name+'.txt')).read_text().split('\f')
 for n in ns:
  b=pages[n-1].encode();p=O/'page-extracts'/f'{name}-p{n}.txt';p.parent.mkdir(exist_ok=True);p.write_bytes(b)
  ex.append({'pdf':name+'.pdf','physical_page':n,'extract':str(p.relative_to(O)),'extract_sha256':sha(b),'pdf_sha256':sha((O/(name+'.pdf')).read_bytes())})
(O/'page-locators.json').write_text(json.dumps(ex,indent=2))
print('Recorded',len(inputs),'inputs,',len(ranges),'source label ranges,',len(ex),'page extracts')
