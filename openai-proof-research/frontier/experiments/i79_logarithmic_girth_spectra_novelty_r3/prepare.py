import pathlib,json,hashlib,re,datetime
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3';E=R/'frontier/experiments/i79_logarithmic_girth_spectra_novelty_r3';C='frontier/sources/i14_spectral_width_novelty_r3/corpus/'
LEDGERS=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
def sha(b):return hashlib.sha256(b).hexdigest()
def rec(p):
 b=(R/p).read_bytes();return dict(path=p,bytes=len(b),sha256=sha(b),mutable=p in LEDGERS)
refs=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/iterations/i72-graph-probability-discovery.md','frontier/iterations/i76-logarithmic-girth-spectra.md','frontier/experiments/i72-parent-verification.json','frontier/experiments/i76-parent-verification.json','frontier/sources/i72_graph_probability_discovery/seal-v1.json','frontier/sources/i72_graph_probability_discovery/corpus-domain.json','frontier/sources/i72_graph_probability_discovery/inventory.json','frontier/sources/i76_logarithmic_girth_spectra/seal-v1.json','frontier/experiments/i76_logarithmic_girth_spectra/verify.py']+LEDGERS
(S/'ledgers').mkdir(exist_ok=True)
for p in LEDGERS:(S/'ledgers'/p.replace('/','__')).write_bytes((R/p).read_bytes())
clean=C+'preprints/GOE-bulk-universality-for-fixed-degree-random-regular-graphs-September-23-2026/build/sections/'
ander=C+'preprints/Fixed-energy-universality-for-weak-Anderson-disorder-on-random-regular-graphs-October-5-2026/build/sections/'
for p in (R/clean).glob('*.tex'):refs.append(str(p.relative_to(R)))
for p in (R/ander).glob('*.tex'):refs.append(str(p.relative_to(R)))
passages=[]
def passage(id,p,a,b,why):
 text=''.join((R/p).read_text().splitlines(keepends=True)[a-1:b]);passages.append(dict(id=id,path=p,start=a,end=b,sha256=sha(text.encode()),bytes=len(text.encode()),text=text,purpose=why));refs.append(p)
for id,file,a,b,why in [
 ('clean-main','01-introduction.tex',10,61,'Unconditioned labelled fixed-degree ensemble and normalization'),
 ('clean-contract','02-preliminaries.tex',146,232,'Spectral prerequisites; not a general locally tree-like theorem'),
 ('clean-count','03-entropy.tex',1,160,'Type counts and simultaneous entropy input'),
 ('clean-logdet','03-entropy.tex',250,269,'Exact coarse-rigidity role in Gaussian entropy determinant'),
 ('clean-limit','04-limits.tex',1,150,'Large microscopic height and mark prerequisites'),
 ('clean-switch','05-switching.tex',1,165,'Finite marked symmetry and limiting insertion'),
 ('clean-dbm','06-dbm.tex',1,125,'Inserted-matrix regularity required before DBM')]:passage(id,clean+file,a,b,why)
for id,file,a,b,why in [
 ('anderson-main','01-introduction.tex',88,153,'Fixed positive disorder, deterministic tree density, unconditioned graph'),
 ('anderson-average','03-local-law.tex',49,145,'Arbitrary real matrix averaging and sampled Ward identity'),
 ('anderson-marked','03-local-law.tex',206,301,'Source already contains exact marked reversal and two-base common Hamiltonian'),
 ('anderson-recursion','03-local-law.tex',398,516,'Source already contains same-realization coupling, multiplier and second moment'),
 ('anderson-descent','03-local-law.tex',518,610,'Fixed-height initialization and geometric height descent'),
 ('anderson-centering','04-marked-entropy.tex',98,173,'Potential bump conditional centering is source work'),
 ('anderson-count','04-marked-entropy.tex',175,271,'Environment count, bin probability and overlap costs'),
 ('anderson-refinements','04-marked-entropy.tex',272,440,'Conditional entropy refinement order'),
 ('anderson-gaussian','05-rigidity.tex',1,140,'Environment precision and Gaussian equality-case input'),
 ('anderson-insert','07-insertion.tex',1,125,'Potential-based insertion already a source operation')]:passage(id,ander+file,a,b,why)
for family,file,a,b,id,why in [
 ('A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026','build/sections/types.tex',103,151,'girth-matchings','Logarithmic girth conditioning and far-switch counting already in corpus'),
 ('A-Torsion-Free-Group-Algebra-That-Is-Not-Directly-Finite-October-4-2026','build/sections/random.tex',223,361,'girth-prescriptions','Uniform prescriptions without inverse event probability'),
 ('A-Torsion-Free-Counterexample-to-Reduced-Baum-Connes-Injectivity-September-23-2026','build/sections/04_analysis.tex',750,770,'voltage-scope','Norm concentration explicitly independent of girth conditioning'),
 ('A-Torsion-Free-Counterexample-to-Reduced-Baum-Connes-Injectivity-September-23-2026','build/sections/04_analysis.tex',850,895,'voltage-selection','Simultaneous existence by union bound, not conditioned spectral universality'),
 ('Deterministic-nonbipartite-Ramanujan-graphs-in-every-fixed-degree-September-23-2026','build/sections/introduction.tex',1,47,'ramanujan','Deterministic extremal-spectrum construction, not point-process theorem')]:passage(id,C+'preprints/'+family+'/'+file,a,b,why)
prefix=str(S.relative_to(R))+'/primary/'
for id,file,a,b,why in [
 ('mww-rarity','mww.txt',25,120,'Uniform labelled model and relative zero-cycle formula'),
 ('mww-proof','mww.txt',320,450,'Actual forward/backward cycle-switch counting and zero-event treatment'),
 ('hy-map','hy.txt',760,924,'Original marked fiber, indicator reversal and measure preservation'),
 ('hy-propositions','hy.txt',1067,1154,'Pointwise fixed-input hypotheses; q wording is not arbitrarily-large statement'),
 ('hy-continuation','hy.txt',1190,1365,'Grid and same-defect involution argument (4.27)-(4.30)'),
 ('hy-q','hy.txt',1835,1953,'Fixed-q sample counts and dependence in deterministic class'),
 ('hy-concentration','hy.txt',3192,3270,'Independent original-fiber concentration, not accepted-fiber independence'),
 ('hhw-main','hhw.txt',67,145,'Current fixed-degree unconditioned bulk theorem and pi normalization'),
 ('hhw-noise','hhw.txt',919,958,'Log-determinant entropy needs only mesoscopic approximation'),
 ('hhw-input','hhw.txt',1505,1585,'Separate spectral events with polynomial failure, imports HY'),
 ('hhw-channel','hhw.txt',1710,1795,'General correlated Gaussian channel still assumes graph count event'),
 ('loop-scope','loop.txt',1470,1530,'Bulk application excludes fixed d; hierarchy characterization not geometry-only'),
 ('growing-scope','growing.txt',76,116,'Polynomially growing degree required'),
 ('almost-scope','almost.txt',163,225,'Weak Gaussian laws allow variance loss'),
 ('cone-scope','cone.txt',214,252,'Shrinking slowly spectral window, not microscopic eigenvalue law'),
 ('typical-scope','typical.txt',108,164,'Typicality defined via uniform regular graphs'),
 ('trees-scope','trees.txt',40,105,'Universal/typical processes distinct from GOE spectral universality'),
 ('edge-scope','edge.txt',90,210,'Fixed degree edge theorem does not claim conditioned bulk law')]:passage(id,prefix+file,a,b,why)
(S/'passages.json').write_text(json.dumps(passages,indent=2,ensure_ascii=False))
# All outside/corpus search bodies have independent byte identities, references below cover decisive inspected text.
(S/'inputs.json').write_text(json.dumps([rec(p) for p in sorted(set(refs)) if not p.startswith(str(S.relative_to(R))+'/')],indent=2))
versions=[]
for p in (S/'primary').glob('*page.html'):
 lines=p.read_text().splitlines(keepends=True);a=next(i for i,l in enumerate(lines) if 'Submission history' in l);b=min(len(lines),a+16);txt=''.join(lines[a:b]);versions.append(dict(path=str(p.relative_to(R)),start=a+1,end=b,text=txt,sha256=sha(txt.encode()),latest=re.findall(r'<strong>\[(v\d+)\]</strong>',txt)[0]))
(S/'versions.json').write_text(json.dumps(versions,indent=2))
(S/'preseal-events.json').write_text(json.dumps([
 {'event':'brief export truncated','retained':'brief-truncated-preseal.txt','correction':'itemId plus contiguous UTF-16 offset retrieval; full brief now has 110282 original UTF-16 units'},
 {'event':'initial T3 read rejected','raw':'Mcp error: -32602: Invalid parameters for tool t3_thread_read: Missing key at [threadId]','correction':'used discovered currentThreadId; no permission request'},
 {'event':'unsupported optional textLimit/unbound textOffset','effect':'returned first 20000 units again; no complete export claimed','correction':'read documented maxCharsPerItem and itemId'},
 {'event':'path typo created empty bootstrap file one level outside owned experiment directory','path':'frontier/experiments/i79_logarithmic_girth_spectra_novelty_r3_bootstrap.tmp','bytes':0,'correction':'immediately removed before any contents or subsequent work; all surviving writes in assigned paths'},
 {'event':'initial exploratory web query response not persisted at call time','queries':['random regular graphs fixed degree bulk universality locally tree like permutation invariant ensembles entropy','random regular graphs conditioned high girth bulk universality GOE'],'effect':'discovery only, no conclusion rests on it; subsequent persisted queries and primary captures supersede it'},
 {'event':'HTTP acquisition','outcome':'all 1033 pinned outside requests and 18 primary requests returned 200; no HTTP failures to suppress'}
],indent=2))
print('inputs',len(set(refs)),'passages',len(passages),'versions',len(versions))
