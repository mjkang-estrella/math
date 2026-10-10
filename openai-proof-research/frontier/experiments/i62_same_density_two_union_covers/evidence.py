"""One-time evidence assembly; verifier is a separate read-only program."""
from pathlib import Path
import hashlib,json,re,requests,concurrent.futures,subprocess,os
R=Path.cwd();S=R/'frontier/sources/i62_same_density_two_union_covers';E=R/'frontier/experiments/i62_same_density_two_union_covers'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def passage(path,start,end,label):
 p=R/path;lines=p.read_text().splitlines(keepends=True);assert 1<=start<=end<=len(lines)
 return dict(file=path,start=start,end=end,label=label,sha256=sha(''.join(lines[start-1:end]).encode()))
pins=json.loads((S/'pinned-manifest.json').read_text());reads=[]
for x in pins:reads.append(passage(x['file'],1,len((R/x['file']).read_text().splitlines()),'Complete selected pinned source file; not a full-corpus read'))
for name,start,end,label in [
 ('li-pdf',1,542,'Li v2 statements and full spectral/coupling proofs'),
 ('park-pdf',218,260,'Park Theorem 3.4 and Corollary 3.5'),
 ('ahpt-pdf',1082,1130,'AHPT Section 8 two-threshold scope'),
 ('fischer-person-pdf',1,244,'Fischer–Person hypotheses, random-union construction and overlap interface'),
 ('fischer-person-pdf',360,413,'Fischer–Person full Theorem 5 proof'),
 ('fkp-pdf',185,221,'Attributed singleton prefix cover'),
 ('lovasz-pdf',1,121,'Ferber–Shapira Section 2 complete greedy-coloring proof'),
 ('talagrand-2010',390,729,'Fractional duality, discrete convexity and explicit downward-closure observation'),
 ('talagrand-2021',20790,20879,'Original 2021 problem, cardinality example, selector consequence')]:
 reads.append(passage(str((S/'literature'/f'{name}.txt').relative_to(R)),start,end,label))
save(S/'read-passages.json',reads)
contracts=[]
def contract(fragment,label,conclusion):
 row=next(x for x in reads if fragment in x['file']);contracts.append(dict(**row,contract=label,permitted_use=conclusion))
contract('00_intro.tex','Original-density versus two-union quantifiers','2^75 unions at same p; two unions with loss 50*512^4, no D.')
contract('01_covering.tex','Integral pair-sampling operation','Many small-bin edges force a cover; 2^12h threshold; full original proof available.')
contract('02_weights.tex','Full signed-kernel operation','Two-row case gives first powers of w; 32 rows give w^16; not interchangeable in bin sum.')
contract('03_density.tex','Density restoration changes union count','Grouping L Bernoulli-p rows gives 32L unions, not two.')
contract('/selector.tex','Simultaneous capture uses inflated color probabilities','D=256 and pi_i=D^i p; no selector at unchanged mean is asserted.')
contract('/rounding.tex','Actual rounding mean interface','Y has mean at most 5*512^4 p=r/5 at target p=r/(25*512^4); unbounded sizes require this comparison.')
contract('/consequences.tex','Two-union companion already available','Mass >1/2 gives cover at p/(50*512^4).')
contract('/li-pdf.txt','External two-row certificate independently reconstructed','Thm1.15 attributed, Thm1.19 dependent coupling does not assert integral smallness.')
contract('/lovasz-pdf.txt','Property B mechanism reconstructed in report','Greedy red-blue coloring yields a separated pair; uniform separation probability exact.')
contract('/talagrand-2021.txt','2021 original problem','Cardinality downset already treated with large q; no factor-two conclusion imported.')
save(S/'source-contracts.json',contracts)
objections=[
('Downward closure could change allowable unions.','Each closure member has an original witness; expand the two witnesses. Also already Talagrand 2010.'),
('Small probability of D complement gives a cheap cover.','Only proved with the explicit rank-dependent A constants. Never used for arbitrary rank.'),
('Critical cores themselves should have small total cost.','False: triangle book, m=ceil(p^-4), independence mass tends to one but mp^3 diverges; optimum p^2.'),
('Random greedy coloring selects fewer critical cores.','For a triangle book every ordering selects every triangle, even after pruning pairs to critical supports.'),
('Boolean/idempotent spectral coefficients have enough exponential decay for Cp.','False for every C>1 by connected uniform petal/core construction C; actual coefficients and capping verified.'),
('Removing even coefficients fixes spectral amplification.','Exact odd generating function (5.8) still diverges.'),
('Construction C refutes D.','No. Its unique critical core has exact optimum p^(2r+1), tending to zero.'),
('Actual two-union families might have no fractional/integral gap.','Five-vertex cardinality downset at p=5/13 has exact fractional 250/507 and integral 1150/2197, but its mass is below half.'),
('Tensor amplification makes that finite counterexample high mass.','Ordinary product lowers mass; no amplification preserving D is proved.'),
('Weighted cardinality two-union coverage only needs total at most two.','Three items 3/5 each disprove it; actual two-bin packing is needed.'),
('Graph and disjoint-core cases should be new accepted findings.','They have explicit classical reductions and do not need new upstream operations; technical only.'),
('Finite search establishes the infinite-quantifier theorem.','No, it covers all downsets through n=5 only at three specified rational p, plus named separate exact cases.'),
('Old sealed artifacts can be refreshed to simplify verification.','No historical writes. Four mutable ledger differences are informational; search scopes remain fixed line multisets.'),
('Prior evidence PASS certifies the analytic theorem.','No. I60 parent replay and I62 verifier are evidence checks; only the two-row input has an author-level independent analytic audit here.')]
save(S/'objections.json',[dict(objection=a,response=b) for a,b in objections])
versions=[]
for p in sorted((S/'literature').glob('*-abs.html')):
 s=p.read_text();idx=s.find('Submission history');flat=re.sub('<[^>]+>',' ',s);flat=re.sub(r'\s+',' ',flat)
 i=flat.find('Submission history');versions.append(dict(file=str(p.relative_to(R)),versions=sorted(set(re.findall(r'\[v\d+\]',s))),history=flat[i:i+650],withdrawn=bool(re.search('withdrawn',s,re.I))))
save(S/'literature/versions.json',versions)
old=json.loads((R/'frontier/sources/i60_threshold_structural_combinatorics_discovery/old-files-watch.json').read_text());watch=json.loads((S/'old-watch.json').read_text());known={x['path'] for x in watch}
for row in old:
 if row['path'] not in known:watch.append(dict(path=row['path'],sha256=sha((R/row['path']).read_bytes())))
save(S/'old-watch.json',watch)
# Specific companion-search scope, fixed to this exact corpus inventory.
cmd=['rg','--no-ignore','-n','-i',r'Talagrand.{0,30}(discrete|selector)|discrete.convexity|fractional.cover|two.colorable|property B',str(R/'frontier/sources/i14_spectral_width_novelty_r3/corpus')]
r=subprocess.run(cmd,capture_output=True,text=True);save(S/'companion-search.json',dict(command=cmd,returncode=r.returncode,lines=sorted(r.stdout.splitlines())))
# Fresh direct retrievals of five exact pinned proof files; no mutable main branch.
selected=[x for x in pins if any(x['path'].endswith(t) for t in ['00_intro.tex','02_weights.tex','03_density.tex','selector.tex','rounding.tex'])]
def fetch(x):
 r=requests.get(x['url'],timeout=35);p=S/'fresh-pinned'/x['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(r.content)
 return dict(url=x['url'],path=x['path'],file=str(p.relative_to(R)),status=r.status_code,sha256=sha(r.content),matches_selected=r.content==(R/x['file']).read_bytes())
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:responses=list(ex.map(fetch,selected))
save(S/'fresh-pinned.json',responses)
# Preserve the unmodified I60 verifier output here, not in its sealed directory.
r=subprocess.run(['python','frontier/experiments/i60_threshold_structural_combinatorics_discovery/verify.py'],capture_output=True,text=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
save(S/'i60-readonly-replay.json',dict(command='PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i60_threshold_structural_combinatorics_discovery/verify.py',exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
print(json.dumps(dict(passages=len(reads),contracts=len(contracts),old_watches=len(watch),fresh_pins=responses,i60_exit=r.returncode),indent=2))
