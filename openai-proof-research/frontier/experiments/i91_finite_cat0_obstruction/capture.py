"""Historical pre-seal capture only. NEVER called by the verifier."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i91_finite_cat0_obstruction'
E=R/'frontier/experiments/i91_finite_cat0_obstruction'
def h(b):return hashlib.sha256(b).hexdigest()
def save(p,x):p.write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
assert not (S/'seal-v1.json').exists()
refs=set(['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json',
 'frontier/iterations/i89-geometric-group-discovery.md','frontier/experiments/i89-parent-verification.json'])
I79='frontier/sources/i79_logarithmic_girth_spectra_novelty_r3'
I89='frontier/sources/i89_geometric_group_discovery'
for n in ('search-domain.json','outside-requests.jsonl','seal-v1.json'):refs.add(I79+'/'+n)
for n in ('seal-v1.json','seal-v1.sha256','passages.json','immutable-references.json','primary/responses.jsonl','primary/responses-more.jsonl'):refs.add(I89+'/'+n)
for n in ('verify.py','checks.py'):refs.add('frontier/experiments/i89_geometric_group_discovery/'+n)
base='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
A=base+'A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/build/sections/'
passages=[]
def passage(path,label,start=1,end=None):
 b=(R/path).read_bytes();ls=b.decode().splitlines(keepends=True);end=end or len(ls)
 body=''.join(ls[start-1:end]);assert 1<=start<=end<=len(ls)
 passages.append({'path':path,'label':label,'start':start,'end':end,'source_sha256':h(b),'passage_sha256':h(body.encode()),'text':body})
 if not path.startswith('frontier/sources/i91_'):refs.add(path)
for p in sorted((R/A).glob('*.tex')):passage(p.relative_to(R).as_posix(),'A complete '+p.name)
AA=base+'An-Artin-group-with-no-geometric-CAT-0-action-September-23-2026/build/sections/'
for n in ('introduction.tex','lengths.tex','sectors.tex','assembly.tex'):passage(AA+n,'Artin complete '+n)
SF=base+'Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/build/sections/'
for n in ('01-introduction.tex','07-conclusion.tex'):passage(SF+n,'Sharp filling complete '+n)
passage(base+'Generalized-Cartan-Hadamard-isoperimetry-and-Euclidean-equality-rigidity-September-23-2026/build/sections/01-introduction.tex','Smooth equality actual hypotheses',1,89)
passage(I89+'/primary/gromov.txt','Gromov scaling/energy primary',1970,2180)
passage(I89+'/primary/kondo.txt','Kondo complete uniform-action section',348,445)
passage(I89+'/primary/ikn.txt','IKN Proposition 2.1',258,295)
passage(I89+'/primary/ikn.txt','IKN Theorem 2.9',660,682)
passage('frontier/sources/i91_finite_cat0_obstruction/primary/berg-nikolaev.txt','Berg Nikolaev exact K=0 primary statement',33,67)
passage('frontier/iterations/i89-geometric-group-discovery.md','Original I89 sections 3-5',75,218)
save(S/'passages.json',passages)
for name in ('gromov','kondo','ikn'):
 for ext in ('pdf','txt'):refs.add(I89+'/primary/'+name+'.'+ext)
save(S/'immutable-references.json',[{'path':p,'sha256':h((R/p).read_bytes())} for p in sorted(refs)])
data=subprocess.check_output(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus'],cwd=R)
(S/'corpus-rg-files.txt').write_text('\n'.join(sorted(data.decode().splitlines()))+'\n')
out=subprocess.check_output([sys.executable,'-B',str(E/'checks.py')],cwd=R)
save(E/'checks-output.json',json.loads(out))
print(json.dumps({'immutable_references':len(refs),'passages':len(passages),'diagnostic_status':json.loads(out)['diagnostics']['status']}))
