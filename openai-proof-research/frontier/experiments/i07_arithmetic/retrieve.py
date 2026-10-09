import json,hashlib,urllib.request,concurrent.futures,datetime
from pathlib import Path
root=Path(__file__).resolve().parents[3]; out=root/'frontier/sources/i07_arithmetic'; pin=json.loads((root/'sources/upstream.json').read_text())['commit']; tree=json.loads((root/'sources/preprints-tree.json').read_text())
assert tree.get('truncated') is False
selection={
'An-unconditional-first-moment':['paper.tex','dispersion.tex'],
'Simultaneous-primitive-roots':['01-introduction.tex'],
'The-joint-Dickman-law': ['introduction.tex','distribution.tex','arithmetic.tex','conclusion.tex','channels.tex'],
'Squarefree-values-of-quartics':['01-introduction.tex','02-sieve.tex','03-affine-counting.tex','04-arithmetic-boxes.tex','05-determinant-cuts.tex','06-lattice-boxes.tex','07-hilbert-bounds.tex','08-quartic-geometry.tex','09-curves.tex','10-parameters.tex','11-tail-proof.tex','12-certificate.tex','13-cyclotomic.tex'],
'Ordinary-two-point-correlations':['introduction.tex','analytic-transfer.tex','03-analytic.tex'],
'The-Quasi-Riemann-Hypothesis-September':['paper.tex'],
'The-Poisson-Dirichlet-Law':['01-introduction.tex','02-preliminaries.tex','03-determinant.tex','06-correlations.tex','07-extraction.tex','09-long-prime-appendix.tex'],
'Weighted-Dilation-Graphs':['02-transference.tex','03-ideal-kernels.tex'],
'Prime-Predecessors-with-an-Even':['main.tex','03-shifted.tex'],
'Primitive-roots-for-every':['01-introduction.tex','07-splitting.tex','08-type-ii.tex']}
entries=[e for e in tree['tree'] if any(k in e['path'] and Path(e['path']).name in v for k,v in selection.items()) and '/vendor/' not in e['path']]
def get(e):
 url=f'https://raw.githubusercontent.com/openai/math/{pin}/'+e['path']; target=out/'pinned'/e['path']; target.parent.mkdir(parents=True,exist_ok=True)
 data=urllib.request.urlopen(url,timeout=90).read(); target.write_bytes(data)
 blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert blob==e['sha'],e['path']
 return {'path':e['path'],'url':url,'local':str(target.relative_to(root)),'sha256':hashlib.sha256(data).hexdigest(),'git_blob':blob,'bytes':len(data)}
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool: rows=list(pool.map(get,entries))
(out/'retrieval-manifest.json').write_text(json.dumps({'pin':pin,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows},indent=2)+'\n')
inputs=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','frontier/README.md','frontier/findings/R006-progression-PD-primitive-root-density.md','frontier/findings/R008-parity-PD-independence.md','frontier/iterations/i03-arithmetic-progressions.md','frontier/iterations/i05-parity-pd.md','frontier/iterations/i06-cubic-reservoir.md','frontier/reviews/i03-arithmetic-progressions-r4.md','frontier/reviews/i05-parity-pd-r2.md','frontier/reviews/i05-parity-novelty-r3.md']
(out/'input-snapshot.json').write_text(json.dumps([{'path':p,'sha256':hashlib.sha256((root/p).read_bytes()).hexdigest()} for p in inputs],indent=2)+'\n')
print(json.dumps({'files':len(rows),'blob_matches':len(rows),'bytes':sum(r['bytes'] for r in rows)}))
