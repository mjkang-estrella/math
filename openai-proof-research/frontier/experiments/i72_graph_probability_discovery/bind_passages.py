"""One-time evidence binding; not part of read-only verification."""
from pathlib import Path
import json,hashlib
R=Path.cwd();S=R/'frontier/sources/i72_graph_probability_discovery';P=S/'pinned/preprints'
items=[]
def add(name,p,a,b,used):
 p=Path(p);lines=p.read_text().splitlines(keepends=True);assert 1<=a<=b<=len(lines)
 t=''.join(lines[a-1:b]);items.append({'id':name,'path':str(p.relative_to(R)),'start':a,'end':b,'text':t,'sha256':hashlib.sha256(t.encode()).hexdigest(),'use':used})
def src(prefix,tail):return next(p for p in P.rglob(tail) if p.relative_to(P).parts[0].startswith(prefix))
for name,prefix,tail,a,b,use in [
('G-main','GOE-bulk','01-introduction.tex',10,62,'unconditioned theorem and normalization'),
('G-spectral','GOE-bulk','02-preliminaries.tex',146,226,'spectral event and exact HY import'),
('G-moments-count','GOE-bulk','03-entropy.tex',1,106,'fixed-dimensional common graph events and actual type-count proof'),
('G-limits-start','GOE-bulk','04-limits.tex',11,54,'marked resolvents and endpoint probabilities'),
('G-switch-identity','GOE-bulk','04-limits.tex',155,219,'finite marked bijection and microscopic rank bound'),
('G-limit-contract','GOE-bulk','04-limits.tex',263,325,'tail and marked-law requirements'),
('G-continuous','GOE-bulk','05-switching.tex',1,108,'permutation/reflection generation and analytic normalization'),
('G-insertion-order','GOE-bulk','05-switching.tex',145,202,'post-n channel growth; cutoffs and conditional approximation'),
('G-dbm-density','GOE-bulk','06-dbm.tex',155,173,'density adjustment contract'),
('A-main','Fixed-energy','01-introduction.tex',88,155,'fixed positive disorder, tree density, no graph conditioning'),
('A-local','Fixed-energy','03-local-law.tex',35,87,'strong arbitrary-graph spectral averaging; 1/w cost'),
('A-recursion','Fixed-energy','03-local-law.tex',175,225,'two-observation conditional empirical recursion and marked switch'),
('A-resolvents','Fixed-energy','03-local-law.tex',300,370,'uniform modification tails and extra far-edge switch'),
('A-centering','Fixed-energy','04-marked-entropy.tex',108,174,'fixed-w potential change and total variation; no clean crossover'),
('P-main','Nonuniqueness','introduction.tex',56,95,'critical operator gap and simultaneous interval'),
('P-sprinkling','Nonuniqueness','preliminaries.tex',494,525,'source blue-edge expansion'),
('P-cluster-count','Nonuniqueness','conclusion.tex',204,270,'source invariant coupled-interval proof'),
('P-critical-laws','Nonuniqueness','consequences.tex',1,115,'stronger already-printed tails and exponential decay'),
('C-critical','No-percolation-at','introduction.tex',24,43,'qualitative critical theorem hypotheses'),
('C-inhom-gluing','No-percolation-at','gluing.tex',11,35,'arbitrary independent probabilities already allowed'),
('W-main','Polynomial-Mixing','introduction.tex',1,67,'exact proposal normalization and uniform theorem'),
('W-strategy','Polynomial-Mixing','introduction.tex',116,150,'conditional slices and aggregate projection mechanism'),
('W-row','Polynomial-Mixing','rows.tex',16,67,'uniform partition heat-flow invariance'),
('W-disjoint','Polynomial-Mixing','disjoint.tex',1,56,'uniform-L2 involution and projection identity'),
]:
 p=src(prefix,tail);add(name,p,a,min(b,len(p.read_text().splitlines())),use)
# Exact unweighted companion range located from labels, avoiding guessed numbering.
p=src('A-Fully-Polynomial','main.tex');lines=p.read_text().splitlines();a=next(i for i,l in enumerate(lines,1) if l.startswith('\\section{Prescribed-degree'));b=next(i for i,l in enumerate(lines,1) if i>a and l.startswith('\\subsection{Constant-fibre'))
add('M-prescribed-degree',p,a,b,'unweighted host guarantee, uniform sampling and no weight encoding')
for name,file,a,b,use in [
('MWW-contract','mww.txt',55,124,'relative girth probability and admissible range'),
('MWW-expectation','mww.txt',150,166,'short-cycle mean'),
('MWW-transport','mww.txt',337,456,'actual forward/backward counts; averages not a uniform transport'),
('HY-geometry','hy-v3.txt',139,179,'probability relative to uniform tree-like class'),
('HY-deloc','hy-v3.txt',209,227,'all-eigenvector normalization and limits of geometric regularity'),
('HY-local-law','hy-v3.txt',930,1009,'spectral scale and fixed polynomial exceptional quantifier'),
('HY-classes','hy-v3.txt',1021,1067,'geometry versus spectral regularity'),
('HY-local-resampling','hy-v3.txt',1070,1151,'good resampling sets and their probabilities'),
('HY-bootstrap','hy-v3.txt',1190,1222,'spectral grid and union accumulation'),
('HY-measure-map','hy-v3.txt',1287,1325,'Proposition 4.12 and measure-preserving identity'),
('H-blue-edge','hutchcroft-hyperbolic-v3.txt',354,423,'Lemma 2.4 proof and nonidentical product BK'),
('H-decay','hutchcroft-l2.txt',260,284,'existing exponential two-point quantitative law'),
]:add(name,S/'primary'/file,a,b,use)
for name,path,a,b,use in [
('I19-obstruction','frontier/iterations/i19-fresh-structural-discovery.md',240,262,'mandatory positive-weight obstruction'),
('I13-fibers','frontier/iterations/i13-fresh-discovery.md',147,193,'mandatory completion/flattening objections'),
('I22-maxent','frontier/iterations/i22-combinatorial-discovery.md',202,240,'conditional entropy law and sampler scope'),
('I39-gap','frontier/iterations/i39-quantum-spectral-discovery.md',1,24,'parked domain and stipulated-source convention'),
('Dyer-model','frontier/sources/i19_fresh_structural_discovery/literature/dyer-muller.txt',135,175,'actual switch model, ergodicity versus counting'),
]:add(name,R/path,a,b,use)
(S/'passages.json').write_text(json.dumps(items,indent=2,ensure_ascii=False)+'\n')
versions=[]
for file,last in [('hy-versions.html','v3'),('hutchcroft-hyperbolic-versions.html','v3'),('hutchcroft-l2-versions.html','v2')]:
 p=S/'primary'/file;lines=p.read_text().splitlines(keepends=True);i=next(i for i,l in enumerate(lines) if 'Submission history' in l);t=''.join(lines[i:i+12]);assert f'<strong>[{last}]</strong>' in t
 versions.append({'path':str(p.relative_to(R)),'latest_displayed':last,'start':i+1,'end':i+12,'text':t,'sha256':hashlib.sha256(t.encode()).hexdigest()})
(S/'versions.json').write_text(json.dumps(versions,indent=2)+'\n');print('passages',len(items),'versions',len(versions))
