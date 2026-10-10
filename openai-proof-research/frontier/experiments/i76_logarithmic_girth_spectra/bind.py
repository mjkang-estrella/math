"""One-time bindings to old evidence; does not copy source bodies."""
import pathlib,json,hashlib,re,subprocess
R=pathlib.Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i76_logarithmic_girth_spectra'
O=R/'frontier/sources/i72_graph_probability_discovery'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(name,obj):
 p=S/name;assert not p.exists();p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
refs=json.loads((S/'source-references.json').read_text())
def path(family,filename):return next(x['local_path'] for x in refs if x['path'].split('/')[1].startswith(family) and x['path'].endswith('/'+filename))
specs=[('mww-relative','frontier/sources/i72_graph_probability_discovery/primary/mww.txt',1,124,'Labelled model, relative probability and regime'),
 ('mww-proof','frontier/sources/i72_graph_probability_discovery/primary/mww.txt',330,487,'Switch count iteration and removal of additive error at zero'),
 ('hy-maps','frontier/sources/i72_graph_probability_discovery/primary/hy-v3.txt',742,925,'Actual mark fibers, I/J indicators, involution and constant fiber weights'),
 ('hy-bootstrap','frontier/sources/i72_graph_probability_discovery/primary/hy-v3.txt',925,1450,'Parameters, pointwise propositions, defect sets and n-squared spectral grid'),
 ('hy-distance','frontier/sources/i72_graph_probability_discovery/primary/hy-v3.txt',1820,1953,'Pointwise mark marginals and arbitrary fixed q probability'),
 ('hy-concentration','frontier/sources/i72_graph_probability_discovery/primary/hy-v3.txt',3192,3373,'Independent Z variables, Azuma, normalization and expectation'),
 ('hy-schur-improvement','frontier/sources/i72_graph_probability_discovery/primary/hy-v3.txt',3434,3757,'Conditional punctured-resolvent comparison and Schur center improvement'),
 ('hy-unclaimed-rigidity','frontier/sources/i72_graph_probability_discovery/primary/hy-v3.txt',3758,3910,'Separate fluctuation averaging: not transferred in I76'),
 ('hy-rigidity-use','frontier/sources/i72_graph_probability_discovery/primary/hy-v3.txt',4365,4495,'Why weak local law is not all-index rigidity')]
for family,filename,start,end,purpose in [
 ('GOE-bulk','02-preliminaries.tex',1,226,'Exact spectral contract and normalization'),
 ('GOE-bulk','03-entropy.tex',1,266,'Type count, quantization, only rigidity invocation at log determinant'),
 ('GOE-bulk','03-entropy.tex',267,428,'Projected entropy, source normalization and means'),
 ('GOE-bulk','04-limits.tex',1,265,'Endpoint bootstrap and fixed two-edge symmetry'),
 ('GOE-bulk','04-limits.tex',269,580,'Microscopic marked law and principal-value constants'),
 ('GOE-bulk','05-switching.tex',1,203,'Fixed-channel action, insertion statement and order of limits'),
 ('GOE-bulk','06-dbm.tex',112,315,'Exact density adjustment and final coordinates'),
 ('Fixed-energy','01-introduction.tex',95,239,'Ensemble, fixed-w quantifiers, GOE normalization'),
 ('Fixed-energy','02-tree.tex',1,95,'Distributional recursion stability and fixed tree threshold'),
 ('Fixed-energy','03-local-law.tex',1,225,'Arbitrary-graph averaging, Ward and same-H recursion'),
 ('Fixed-energy','03-local-law.tex',225,548,'Stub maps, cut-edge re-pairing, internal potential coupling, two moments'),
 ('Fixed-energy','03-local-law.tex',549,712,'Height descent, augmented limits, intercept uniform integrability'),
 ('Fixed-energy','04-marked-entropy.tex',1,239,'Microscopic normalization, bump centering and environment count'),
 ('Fixed-energy','04-marked-entropy.tex',240,407,'Conditioned entropy, overlapping environment cancellation and limits'),
 ('Fixed-energy','05-rigidity.tex',1,523,'Pointwise precision, entropy equality, centering and iid ergodicity interfaces'),
 ('Fixed-energy','06-resolvents.tex',1,573,'Compression tails, signed principal values, same-environment constants and potential maps'),
 ('Fixed-energy','07-insertion.tex',1,687,'Coefficient centering, two cuts, weighted Schur and Gaussian replacement'),
 ('Fixed-energy','08-dbm.tex',1,504,'Finite-matrix density normalization and Laplace identification'),
 ('Fixed-energy','09-goe-counts.tex',1,164,'GOE reference compact-count exponential moment')]:
 specs.append((family+'-'+filename+'-'+str(start),path(family,filename),start,end,purpose))
passages=[]
for id,p,start,end,purpose in specs:
 lines=(R/p).read_text().splitlines(keepends=True);assert 1<=start<=end<=len(lines),(p,len(lines),end)
 b=''.join(lines[start-1:end]).encode()
 passages.append(dict(id=id,path=p,start=start,end=end,bytes=len(b),sha256=sha(b),purpose=purpose))
save('passages.json',passages)
domain=sorted(x['local_path'] for x in refs if '/GOE-bulk-' in x['path'] and '/sections/' in x['path'])
pattern='rigid|spectral-input|delocal|quantile'
run=subprocess.run(['rg','-n',pattern,*domain],cwd=R,capture_output=True,text=True)
assert run.returncode==0,run.stderr
hits=[]
for line in run.stdout.splitlines():
 p,i,t=line.split(':',2);hits.append([p,int(i),t])
save('interface-search.json',dict(domain=domain,pattern=pattern,hits=hits,semantics='Complete line multiset on the fixed clean-section domain, not worldwide novelty evidence.'))
html=S/'responses/hy-current.html';lines=html.read_text().splitlines(keepends=True)
text=''.join(lines[119:121])+''.join(lines[172:180])
save('version-binding.json',dict(path=str(html.relative_to(R)),latest_displayed='v3',ranges=[[120,121],[173,180]],text=text,sha256=sha(text.encode())))
print(json.dumps({'passages':len(passages),'interface_search_hits':len(hits)}))
