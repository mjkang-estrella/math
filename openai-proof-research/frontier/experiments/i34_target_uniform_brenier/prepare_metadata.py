"""Build provenance metadata from recorded reads and existing immutable manifests."""
import pathlib,json,hashlib,re
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i34_target_uniform_brenier';C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def dump(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def ident(p):b=p.read_bytes();return dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
old=json.loads((R/'frontier/sources/i33_density_robust_brenier/source-manifest.json').read_text());selected=[r for r in old if '/Sharp-One-Third-' in r['path']];dump(S/'source-manifest.json',selected)
cm=json.loads((R/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text());tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text())
titles=sorted({r['path'].split('/')[1] for r in tree['tree'] if r['path'].startswith('preprints/') and len(r['path'].split('/'))>=2})
screen=[x for x in titles if re.search('brenier|transport|entrop',x,re.I)]
hits=[]
for row in cm['files']:
 p=C/row['path'];t=p.read_text(errors='replace')
 if re.search(r'Brenier.{0,35}stability|stability.{0,35}Brenier|entropic.{0,35}bias',t,re.I):hits.append(row['path'])
dump(S/'inventory-screen.json',dict(pin=cm['pin'],manuscripts=len(titles),text_files=len(cm['files']),truncated=tree['truncated'],title_screen=screen,text_hits=hits,scope='Complete path/title/text screen only; semantic reading is limited to read-passages.json'))
contracts=[]
def contract(path,labels,scope,limits):
 p=R/path;contracts.append(dict(**ident(p),labels=labels,scope=scope,limits=limits))
base='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/build/source/sections/'
for n,lab,sc,lim in [
 ('cells.tex',['cells:calculus','cells:weights'],'Joint cell calculus with continuous test integrands, connected graph, normalized mass prescription','Uniform-source estimates are stipulated; weighted integrands reuse this operation; no quantitative inverse estimate.'),
 ('moments.tex',['moments:derivative','moments:midpoint'],'Uniform-source moment inequality and exact midpoint domination','Not extended to arbitrary comparable densities; I33 obstruction audited.'),
 ('finite_stability.tex',['finite:potentials'],'Optimal target coupling, collision exclusion in interior, normalized potential estimate','Uniform-source moment premise only; not a bounded-density linear estimate.'),
 ('gradient.tex',['gradient:interpolation','gradient:extension'],'Slicing, compactness, restricted Fenchel optimality and uniqueness','Qualitative density/target limits do not erase atom-count constants.'),
 ('sharpness.tex',['cells:optimality','sharpness:exponent'],'Optimality of finite maxima and sharp uniform-source example','Premise; no upstream audit.')]:contract(base+n,lab,sc,lim)
lit='frontier/sources/i33_density_robust_brenier/literature/'
for n,lab,sc,lim in [
 ('lm-v3.txt',['Theorem 2.1','Proposition 2.2'],'Variance coercivity under bounded comparison, convex gradient interpolation','Not linear potential stability in W2.'),
 ('ruan-v1.txt',['Definition 3','Section 11','Theorem 8'],'Target repair, correlation gap, quarter-power map estimate','Density size remains in proof constants; W1 versus W2 distinguished.'),
 ('wang-v1.txt',['Lemmas 6–8','Theorem 1 proof'],'Compensated nonnegative Moreau error, gap coercivity, optimal-target gluing','Gives quarter-power in stated broad class.'),
 ('merigot-v1.txt',['Theorem 3.4','Section 4'],'Proximal arbitrary-plan conditioning, configurationwise entropic cost bias','Does not give target-uniform squared bias O(epsilon).'),
 ('ford-v1.txt',['Proposition 5.2'],'Separated-rectangle sharpness construction','Density vanishes away from its rectangle union; not admissible for Q.'),
 ('bk-v2.txt',['Theorem 1.3','Section 2','Lemma 2.1'],'Acyclic exchange digraph and atom-dependent mass reassignment','Quadratic specialization proved in audit, not quoted with different original constants.'),
 ('dnwp-v1.txt',['equations (7)–(12)','Theorem 3.1','Proposition 4.1','Theorem 4.3','Appendix A'],'Relative-reference dual, Hessian identity, target-uniform entropic stability, pairwise bias/coarea proof','Equation (22) needs counting-measure dual shift; fixed-configuration constants and limiting order retained.')]:contract(lit+n,lab,sc,lim)
for n,lab,sc,lim in [
 ('delalande.txt',['Section 2.1','Theorem 2.1','Corollary 2.2'],'Counting-reference finite dual and o(epsilon) normalized corrections','Fixed Hölder density and finite target; constants depend on target geometry, masses, count and source regularity.'),
 ('altschuler-v1.txt',['Theorem 1.3','Section 2.2'],'Counting-reference asymptotic convention','Fixed configuration; half-cost/inverse-temperature conversion required.'),
 ('mulcahy-v1.txt',['Assumption 1','Main Theorem 1'],'Hypothesis screen of score expansion','No proof dependency: strong log-concavity/full support/higher derivatives exclude Q target class.')]:contract('frontier/sources/i34_target_uniform_brenier/literature/'+n,lab,sc,lim)
dump(S/'contracts.json',contracts)
dump(S/'audit-verdicts.json',dict(original_i33_obstruction='PASS without mathematical repair',original_i33_finite_atom_theorem='PASS without mathematical repair',external_interface='Counting-measure shift required when applying Delalande to DNWP relative-reference coordinates; original I33 proof objects do not depend on this',Q='UNPROVED AND NOT REFUTED',new_results='Author technical deductions and precisely scoped obstructions; later fresh full-proof and significance reviews still required for any substantial theorem'))
dump(S/'provenance-notes.json',dict(initial_search='Initial exploratory web response was not serialized. search1.json is the later exact request/response, not a reconstruction of the first.',prior_failures='I33 failed publisher responses retained and verified as historical; no fresh published DNWP comparison claimed.',diagnostic_initial_failure='SymPy import unavailable. Final script uses standard library only. No package installed.',read_log='Line ranges use Python str.splitlines(keepends=True), including form-feed separators in pdftotext output. Re-read overlapping ranges fill initially truncated presentation sections. Full inventory search is not semantic reading.',mutation_scope='Only assigned I34 report, sources and experiments; prior scripts loaded with non-main runpy name, no prior writers invoked.',approval='No subagents, shared-index changes, staging, commits or publication.'))
print(json.dumps(dict(selected=len(selected),contracts=len(contracts),screen_titles=len(screen),screen_hits=len(hits))))
