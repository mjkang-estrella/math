"""Preseal evidence preparation only. Never run by verify.py."""
from pathlib import Path
import json,hashlib,subprocess
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i90_anchored_rank_approximation'
def digest(b):return hashlib.sha256(b).hexdigest()
def write(n,x):(S/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
D=json.loads((ROOT/'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json').read_text())
fams=dict(F='Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026',C='The-cotype-cotype-conjecture-under-the-approximation-property-September-23-2026',E='Counterexamples-to-the-duality-conjecture-for-metric-entropy-September-24-2026',U='An-explicit-obstruction-to-nuclear-norm-ultrapower-embeddings-September-23-2026')
write('families.json',fams)
write('selected-inventory.json',[dict(r,alias=next(a for a,f in fams.items() if f==r['path'].split('/')[1])) for r in D if r['path'].split('/')[1] in fams.values()])
reads=[]
def add(path,scope,start=1,end=None):
 p=ROOT/path;b=p.read_bytes();ls=b.decode().splitlines(keepends=True);end=len(ls) if end is None else end
 assert 1<=start<=end<=len(ls),(path,start,end,len(ls))
 reads.append(dict(path=path,scope=scope,start=start,end=end,line_convention='str.splitlines(keepends=True)',sha256=digest(b),passage_sha256=digest(''.join(ls[start-1:end]).encode())))
for r in D:
 path=r['path'];local=r['local'];fam=path.split('/')[1];filename=path.rsplit('/',1)[-1]
 if fam==fams['F'] and (('/sections/' in path and path.endswith('.tex')) or path.endswith('/build/main.tex')):add(local,'complete proof section or main-file contract')
 if fam==fams['C'] and filename in ['introduction.tex','preliminaries.tex','coefficient.tex','walsh.tex','approximation.tex']:add(local,'complete relevant companion operation')
 if fam==fams['E'] and filename in ['02-matrix-contract.tex','03-compression.tex']:add(local,'complete matrix/signed-compression operation')
 if fam==fams['U'] and filename=='nuclear-finiteness.tex':add(local,'complete nuclear-finiteness operation; screened, unused')
 if fam==fams['F'] and path.endswith('.pdf'):add(local,'PDF operative signed-measure, walk, edge-test and abstract-criterion variant comparison',626,986)
add('frontier/iterations/i88-nonlinear-banach-discovery.md','complete original report, supplied verbatim and hash-checked')
add('frontier/experiments/i88_nonlinear_banach_discovery/verify.py','complete original verifier')
add('frontier/experiments/i88_nonlinear_banach_discovery/diagnostics.py','complete original diagnostic')
add('frontier/sources/i88_nonlinear_banach_discovery/external/local-reflexivity.txt','actual Theorem 2.4 and immediate context',262,280)
ext='frontier/sources/i90_anchored_rank_approximation/external/'
for name,lo,hi,scope in [('naor.txt',199,296,'Proposition 6, Remark 7 and complete proof'),('graph.txt',1400,1534,'Algorithm 1, root-path procedure, Lemma 58 and complete consistency proof'),('godefroy-ozawa.txt',199,225,'Proposition 7 and complete proof plus scope'),('well-conditioned.txt',257,560,'Sections 3.1 and 3.2: basis construction, Auerbach comparison, row sampling and proof'),('subset-selection.txt',182,230,'spanning-set antecedent and theorem, scoped comparison'),('subset-selection.txt',580,625,'sensitivity definition and mechanism'),('subset-selection.txt',2930,2960,'Lemma 8.20 sampling statement, comparison only')]:add(ext+name,scope,lo,hi)
write('read-manifest.json',reads)
refs=set(r['path'] for r in reads if not r['path'].startswith('frontier/sources/i90_'))
refs.update(['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','frontier/iterations/iteration88-nonlinear-banach-discovery-task.json','frontier/experiments/i88-parent-verification.json','frontier/sources/i88_nonlinear_banach_discovery/seal.json','frontier/sources/i88_nonlinear_banach_discovery/search-domain.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl'])
write('immutable-references.json',[dict(path=p,sha256=digest((ROOT/p).read_bytes())) for p in sorted(refs)])
# Inventory exactly as requested, from rg; no copied bodies.
r=subprocess.run(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus'],cwd=ROOT,capture_output=True,check=True)
(S/'i14-rg-inventory.txt').write_text('\n'.join(sorted(r.stdout.decode().splitlines()))+'\n')
write('source-comparison.json',dict(domain='all 10373 original positions via immutable I79 map; seven actual F proof sections plus main file, operative PDF comparison',families=fams,read_records=len(reads),not_claimed='semantic exhaustion; full off-family proofs; external worldwide novelty',variants=[dict(path=r['path'],local=r['local'],sha256=r['sha256']) for r in D if r['path'].split('/')[1] in fams.values() and r['path'].endswith('.pdf')]))
write('external/versions.json',dict(graph=dict(arxiv='2006.12760v1',date='2020-06-23',locator='Section 6.1.2 Algorithm 1 and Lemma 58',published_locator='F cites Algorithm 6.1 and Lemma 6.3; publication not substituted for retained preprint'),naor=dict(arxiv_metadata='2009.11373v2',date='2020-09-27',body='Author-hosted PDF identified by URL/hash; not asserted byte-identical to arXiv v2'),subset_selection=dict(arxiv='2304.09217v1',date='2023-04-18'),well_conditioned=dict(publication='SIAM J. Comput. 38(5) (2009), 2060–2078',body='Author-hosted publisher PDF'),godefroy_ozawa=dict(arxiv='1201.0847v2',body='Explicit v2 URL'),local_reflexivity=dict(body='Inherited I88 primary Goucher–Kania PDF and text; checked Theorem 2.4')))
print(len(reads),'read records;',len(refs),'immutable references')
