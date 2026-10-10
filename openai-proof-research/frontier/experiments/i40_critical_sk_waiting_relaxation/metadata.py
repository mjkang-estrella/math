"""One-time read/contract metadata, not a source acquisition or a seal refresh."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i40_critical_sk_waiting_relaxation'
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
assert not (S/'artifact-seal.json').exists()
rows=json.loads((S/'selected-pinned.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
def source(prefix,ending):
 hits=[r for r in rows if r['path'].split('/')[1].startswith(prefix) and r['path'].endswith('/'+ending)]
 assert len(hits)==1,(prefix,ending)
 return hits[0]
QU='Universality-of-critical-quench';FU='Functional-universality-of-critical-SK';CM='Critical-mixing';CS='Critical-slowing'
reads=[];contracts=[]
def add(prefix,ending,ranges,note,labels=()):
 row=source(prefix,ending);p=C/row['path'];lines=p.read_bytes().splitlines(keepends=True)
 spans=[]
 for lo,hi in ranges:
  assert 1<=lo<=hi<=len(lines),(ending,lo,hi,len(lines))
  spans.append({'first':lo,'last':hi,'sha256':sha(b''.join(lines[lo-1:hi]))})
 reads.append({'kind':'pinned','path':str(p.relative_to(R)),'sha256':row['sha256'],'ranges':spans,'purpose':note,'coverage':'Only listed ranges are claimed as read; selection is not full reading.'})
 for label in labels:
  matches=[i for i,line in enumerate(lines,1) if ('\\label{'+label+'}').encode() in line]
  assert len(matches)==1 and any(a<=matches[0]<=b for a,b in ranges),(label,matches)
  lo=max(1,matches[0]-2);hi=min(len(lines),matches[0]+24)
  excerpt=b''.join(lines[lo-1:hi])
  contracts.append({'source_path':row['path'],'raw_url':row['url'],'git_blob':row['git_blob'],'file_sha256':row['sha256'],'label':label,'label_line':matches[0],'excerpt_first':lo,'excerpt_last':hi,'excerpt_sha256':sha(excerpt),'excerpt':excerpt.decode(),'contract_and_use':note,'scope':'Statement excerpt must be read with proof passages and the exact contracts in report section 1; upstream truth is assumed.'})
add(QU,'01-introduction.tex',[(1,296)],'Both laws; compact positive-time trace convergence and limiting relaxation, not W.', ['thm:main','eq:edge-semigroup'])
add(QU,'02-background.tex',[(1,219)],'Rate-one clock, edge coordinates, varying-space and represented-subsequence conventions.',['prop:stationary-inputs','eq:relaxed-liminf','eq:relaxed-recovery'])
add(QU,'03-edge-estimates.tex',[(1,295)],'Gaussian posterior contracts, Haar-biased law, fixed scale threshold. No Rademacher posterior transfer is asserted.',['edge:haar-bias','prop:edge-estimates','edge:scale-range','edge:variance-estimates','edge:threshold-convention'])
add(QU,'04-warming.tex',[(1,1623)],'Entire proof: arbitrary-initial-law Gaussian entropy and kernel warming, all fixed positive times, confidence events.',['thm:warming','warm:kernel','warm:entropy'])
add(QU,'05-gaussian-limits.tex',[(1,1011)],'Entire proof: common cylinders, bounded resolvents, strong-input semigroups, all-edge squared tails, weak densities, escape proof.',['prop:gaussian-subsequence','glim:common-approximation','glim:optimizer-liminf','glim:semigroup-strong','glim:static-tail','glim:tail-haar','glim:limit-static-tail','glim:relaxation','prop:uniform-seed-escape'])
add(QU,'09-replacement.tex',[(1,934)],'Entire replacement section including cutoff marks and forward compensation. Fixed rectangles/polynomial endpoint tests; no uniform late-time or exponential endpoint-weight extension.',['repl:history-derivatives','repl:test-class','repl:comparison','repl:both-cutoffs'])
add(FU,'02-edge-law.tex',[(154,282)],'Conditioned spherical edge law and polynomial moments.',['prop:edge-conditioned-law','eq:edge-coordinate-moments'])
add(FU,'03-observations.tex',[(140,274)],'Actual replica comparison and static cube marginals, not catalogue abstracts.',['lem:observations-replicas','cor:observations-static'])
add(FU,'05-gradient.tex',[(1,627)],'Full closed-form proof, smoothing and domain; constant kernel gives limit ergodicity.',['prop:gradient-domain','lem:gradient-smoothing'])
add(FU,'06-microscopic.tex',[(790,1062)],'Recovery, positivity, divergence and relaxed-energy proofs. Restricted liminf is not arbitrary-sequence norm compactness.',['lem:micro-recovery','lem:micro-positivity','lem:micro-divergence','thm:micro-relaxation'])
add(FU,'09-functional.tex',[(1,316)],'Positive spectral-measure passage and functional trace convergence; no waiting-time density claim.',['lem:functional-spectral','prop:functional-identification'])
add(CM,'introduction.tex',[(1,140)],'Full exponent-slack theorem and site-attempt clock conventions.',['eq:clock-conventions','thm:main'])
add(CM,'cap-entropy.tex',[(1,160),(300,345),(654,700),(851,880)],'Capacity/layer reduction; first entropy scale sqrt(log n); product logarithm and final slack.',['cap:layer-lemma','cap:first-entropy-scale','cap:product-entropy-bound','cap:thm-lsi'])
add(CS,'introduction.tex',[(1,180)],'Linear-test Rayleigh scope versus whole gap and mixing bounds.',['thm:linear-scale','thm:mixing'])
def local(path,ranges,note,kind='frozen'):
 p=(S/'frozen'/path) if kind=='frozen' else S/'literature'/path
 lines=p.read_bytes().splitlines(keepends=True);spans=[]
 for lo,hi in ranges:
  hi=len(lines) if hi is None else hi
  assert 1<=lo<=hi<=len(lines),(path,lo,hi,len(lines))
  spans.append({'first':lo,'last':hi,'sha256':sha(b''.join(lines[lo-1:hi]))})
 reads.append({'kind':kind,'path':str(p.relative_to(R)),'sha256':sha(p.read_bytes()),'ranges':spans,'purpose':note})
local('AGENTS.md',[(1,None)],'Project authorization and research gate.')
local('sources/upstream.json',[(1,None)],'Immutable upstream pin.')
local('frontier/iterations/i39-quantum-spectral-discovery.md',[(1,None)],'Full I39 deductions, W contract, countermodel, unresolved objections.')
local('frontier/reviews/i38-propeller-stability-novelty-r3.md',[(1,None)],'Full substantiality comparison; arbitrary vanishing-label activation versus quadratic cost.')
local('frontier/reviews/i25-rooted-entropy-novelty-r3.md',[(1,None)],'R011 significance gate; separator compensation is a missing operation.')
local('frontier/reviews/i30-einstein-metric-stability-novelty-r3.md',[(60,105)],'Clarke/Tian-Wang technical reduction.')
local('frontier/reviews/i36-common-geometric-avoidance-novelty-r3.md',[(1,65)],'KP plus local routing operation-level comparison.')
local('langevin-v2.pdf.txt',[(1,150),(300,415)],'Theorem 1.1; fixed T and piecewise-frozen approximation proof.','literature')
local('diffusions-v2.pdf.txt',[(1,100),(145,290),(1018,1062)],'Model/theorem and stochastic Taylor proof: constants and dimension threshold depend on T.','literature')
local('chatterjee-v1.pdf.txt',[(1,20)],'Identity error retained: different paper, not cited 2006 theorem.','literature')
local('chatterjee-correct-v3.pdf.txt',[(35,130),(227,290)],'Correct Theorem 1.1 and derivative replacement proof.','literature')
local('wang-v2.pdf.txt',[(880,1000)],'All-field covariance/entropic stability and subcritical localization.','literature')
local('billoire-v3.pdf.txt',[(1,45),(140,230)],'Numerical equilibrium relaxation; normalization and empirical scaling, not W proof.','literature')
for name,obj in [('read-passages.json',reads),('contracts.json',contracts)]:
 p=S/name;assert not p.exists();p.write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps({'read_passages':len(reads),'source_labels':len(contracts)}))
