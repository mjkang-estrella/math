#!/usr/bin/env python3
"""Build only the I50 evidence records from already retrieved/read bytes."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i50_hard_moment_quantitative_stability_r2';old=R/'frontier/sources/i49_hard_moment_quantitative_stability'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(name,obj):(S/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
inputs=json.loads((S/'frozen-inputs.json').read_text());known={r['path'] for r in inputs}
extra=[*old.glob('corpus-search-*.txt'),*old.glob('vendor/*.whl')]
for p in extra:
 path=str(p.relative_to(R))
 if path in known:continue
 b=p.read_bytes();dst=S/'frozen'/path;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b);inputs.append({'path':path,'sha256':sha(b),'bytes':len(b),'mutable':False})
write('frozen-inputs.json',sorted(inputs,key=lambda x:x['path']))
passages=[]
def passage(src,lo,hi,use):
 p=S/src;b=p.read_bytes();lines=b.splitlines(keepends=True);hi=hi or len(lines);assert 1<=lo<=hi<=len(lines)
 dest=f'passages/{len(passages):03}.txt';(S/dest).parent.mkdir(exist_ok=True);ex=b''.join(lines[lo-1:hi]);(S/dest).write_bytes(ex)
 passages.append({'source':src,'source_sha256':sha(b),'first_line':lo,'last_line':hi,'extract':dest,'sha256':sha(ex),'bytes':len(ex),'use':use,'status':'actual passage read; not a claim to read the rest of the source'})
for fn,use in [
 ('frontier/iterations/i49-hard-moment-quantitative-stability.md','Complete original proof, diagnostics, evidence and quantifiers'),
 ('frontier/iterations/i46-quantitative-logarithmic-stability.md','Complete prior construction A budget and boundary of conditional result; no renewed planar proof audit'),
 ('frontier/reviews/i47-planar-logarithmic-stability-r2.md','Complete prior proof disposition and conditional field audit'),
 ('frontier/reviews/i48-planar-logarithmic-stability-novelty.md','Complete prior contribution disposition; no new significance verdict'),
 ('frontier/experiments/i49-parent-verification.json','Exact initial failure, raw retry and in-memory normalization outcomes'),
 ('AGENTS.md','Project instructions'),
 ('sources/upstream.json','Accepted immutable pin')]:passage('frozen/'+fn,1,None,use)
passage('frozen/frontier/iterations/i44-logarithmic-equality-polytopes.md',230,490,'Relevant hard moment, tensor completion and boundary mechanisms')
passage('frozen/frontier/reviews/i45-logarithmic-equality-r2.md',1,305,'Prior attributed symmetric compactness/completion/contact audit')
prefix='frozen/frontier/sources/i49_hard_moment_quantitative_stability/pinned/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/'
for name in ['tensor','identities','variance','density','moment','reduction','measure']:passage(prefix+name+'.tex',1,None,'Actual pinned proof operations; accepted premises and companion consequences')
passage(prefix+'introduction.tex',1,170,'Actual theorem statement and premise scope')
for fn,ranges in {
 'centered-v2.txt':[(720,835,'Linear-tilt compactness proof checked against quadratic-tilt use'),(925,1100,'Full retained completion and index contractions'),(1290,1495,'Positive joint contact measures and signed boundary passage')],
 'berman.txt':[(120,170,'Compact arbitrary-target theorem'),(1209,1307,'Variational existence, local and global regularity, uniqueness proof'),(1546,1581,'Interior section regularity theorem and proof')],
 'bonnet.txt':[(65,200,'Essential continuity and stability theorem hypotheses'),(680,848,'Constrained comparison and truncation proof'),(925,1040,'Growth completion and main stability proof')],
 'cule.txt':[(125,355,'Proposition 2 and actual convergence proof')],
 'figalli.txt':[(1,205,'Interior theorem and normalized section proof'),(205,220,'Local to global covering in interior proof')],
 'klartag.txt':[(45,85,'Hard target assumptions and trace cap'),(1270,1373,'Diffusion covariance bound and removal of smooth boundary assumptions')],
 'hug-schneider.txt':[(1,275,'Actual BL surface-area theorem and parallel-volume proof')],
 'fmp.txt':[(1,180,'Perimeter orientation, asymmetry normalization and theorem'),(1396,1575,'Cap lemma and actual main proof including affine normalization')],
 'klr.txt':[(1830,1985,'Actual Hessian-Bochner companion proof')]
}.items():
 for lo,hi,use in ranges:passage('primary/'+fn,lo,hi,use)
write('read-passages.json',passages)
versions=[]
for fn,version in [('centered-v2.txt','arXiv:2610.10152v2; 8 October 2026'),('bonnet.txt','arXiv:2604.09914v1'),('klr.txt','arXiv:2507.12099v3')]:
 p=S/'primary'/fn;b=p.read_bytes();lines=[l for l in b.decode().splitlines() if 'arXiv:' in l][:3]
 versions.append({'source':'primary/'+fn,'sha256':sha(b),'version':version,'literal_version_lines':lines})
for fn in ['centered-current.html','bonnet-current.html']:
 p=S/'primary'/fn;b=p.read_bytes();lines=[l for l in b.decode().splitlines() if ('last revised' in l or 'Submitted on' in l or 'citation_date' in l or 'citation_arxiv_id' in l)]
 versions.append({'source':'primary/'+fn,'sha256':sha(b),'literal_version_lines':lines})
write('versions.json',versions)
corpusrel='frontier/sources/i14_spectral_width_novelty_r3/corpus'
patterns=[r'quantitative.{0,70}logarithmic.{0,30}(Brunn|Minkowski)|logarithmic.{0,70}stability',r'finite.defect.{0,40}moment|normal.{0,30}BV|moment.{0,30}product.{0,30}stability',r'eq:tensor-squares|eq:W-gradient|lem:density']
searches=[]
for i,pat in enumerate(patterns):
 run=subprocess.run(['rg','--no-ignore','-n','-i',pat,corpusrel],cwd=R,capture_output=True);fn=f'corpus-search-{i}.txt';(S/fn).write_bytes(run.stdout)
 searches.append({'pattern':pat,'output':fn,'sha256':sha(run.stdout),'returncode':run.returncode,'lines':len(run.stdout.splitlines()),'replay_comparison':'sorted line multiset preserving duplicate lines; not raw byte order'})
write('corpus-search.json',searches)
write('execution-notes.json',{
 'initial_inspection_failure':{'command_scope':'read-only inspection','cause':'one initial exec command omitted workdir and searched the parent directory','outcome':'No source files were written; subsequent commands use project root explicitly'},
 'independent_check_preparation':{'failed_version':'development/check-initial-syntax-error.py','observed_failure':'SyntaxError: unmatched parenthesis on the core-exponent assertion; no assertions had executed','corrections':['Removed the unmatched parenthesis','Before executing corrected script, corrected the interval fixture derivative from twice the actual density to the directly integrated symmetric energy derivative'],'analytic_claim_changes':False,'final_exact_assertions':310},
 'parent_I49':{'record':'frozen/frontier/experiments/i49-parent-verification.json','initial_vanilla':'FAILED: order-sensitive raw rg stdout','later_vanilla_retry':'PASS as recorded by parent','parent_normalized_replay':'PASS, one in-memory ordering replacement','I50_replay':'PASS with same one-line ordering normalization; never described as vanilla'},
 'network':{'fresh_responses':13,'successes':13,'failures':0,'PDFs':9,'all_match_I49_bytes':True},
 'scope':'Finite checks and byte integrity are separate from the analytic audit; no significance verdict',
 'write_scope':['frontier/reviews/i50-hard-moment-quantitative-stability-r2.md','frontier/sources/i50_hard_moment_quantitative_stability_r2/','frontier/experiments/i50_hard_moment_quantitative_stability_r2/']})
write('source-contracts.json',[
 {'source':'Pinned logarithmic manuscript at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','contract':'Accepted theorem and proof operations, read in actual source; no upstream truth audit','application':'Report §§2–3'},
 {'source':'LSX 2610.10152v2','contract':'Completion and contact machinery attributed and independently checked; external nonsymmetric theorem not assumed','application':'Report §§2–3'},
 {'source':'Berman–Berndtsson; Bonnet–Rubinstein; Cule–Samworth; FJM','contract':'Quadratic tilt has arbitrary compact convex target and positive ambient smooth density; centered probabilities and essentially continuous source potentials; section geometry and strict-convexity modulus checked','application':'Existence only, not final rate, report §3.1'},
 {'source':'Klartag Theorem 1','contract':'Bounded convex hard target, smooth convex bounded log-density; boundary smoothness eliminated in actual proof','application':'Dimension-only cap, coercivity and determinant budgets after John normalization, report §4'},
 {'source':'Hug–Schneider Theorem 1.1/(1.2)','contract':'Uniform outer bounds including parallel radius two; bounded-Lipschitz metric, not total variation','application':'Report §§5–7'},
 {'source':'FMP Theorem 1.1','contract':'E=A, Wulff shape B, P_B(A)=n V1(A,B); finite perimeter; translated volume-matched asymmetry','application':'Translation removed by symmetry/convexity; cap gives Hausdorff, report §7'},
 {'source':'KLR Proposition 4.8','contract':'Actual compact-test Hessian-Bochner antecedent, no new hard-field theorem inferred','application':'Dependency credit only'},
 {'source':'I46/I47/I48','contract':'Prior planar status and conditional budgets preserved; no planar revisit or independent significance determination','application':'Historical premise boundary'}])
print(json.dumps({'frozen_inputs':len(inputs),'read_records':len(passages),'corpus_searches':len(searches),'versions':len(versions)},indent=2))
