"""Freeze the significance comparison evidence; never edits prior-round artifacts."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i36_common_geometric_avoidance_novelty_r3'
A=ROOT/'frontier/sources/i36_harmonic_analysis_discovery'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(name,obj):(S/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
inputs=json.loads((S/'input-manifest.json').read_text());paths={r['path'] for r in inputs}
def bind(p):
 p=Path(p);p=p if p.is_absolute() else ROOT/p
 rel=str(p.relative_to(ROOT))
 if rel not in paths:
  b=p.read_bytes();inputs.append({'path':rel,'sha256':sha(b),'bytes':len(b),'mutable':False});paths.add(rel)
 return rel
# Bind every prior artifact already monitored before reproduction, including original seals.
rep=json.loads((ROOT/'frontier/experiments/i36_common_geometric_avoidance_novelty_r3/prior-reproduction.json').read_text())
for p,h in rep['before_after_sha256'].items():
 bind(p);assert sha((ROOT/p).read_bytes())==h
priors=['frontier/iterations/i02-crossfield.md','frontier/reviews/i02-crossfield-r2.md','frontier/reviews/i14-spectral-width-novelty-r3.md','frontier/reviews/i15-odd-order-topology-novelty-r3.md','frontier/reviews/i17-six-point-ramsey-novelty-r3.md','frontier/reviews/i30-einstein-metric-stability-novelty-r3.md','frontier/reviews/i25-rooted-entropy-novelty-r3.md','frontier/findings/R011-rooted-matching-entropy.md','frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json']
for p in priors:bind(p)
pins=[r for r in json.loads((ROOT/'frontier/sources/i36_common_geometric_avoidance_r2/pinned-manifest.json').read_text()) if 'geometric-case' in r['path'] or 'dyadic-case' in r['path']]
write('pinned-manifest.json',pins)
passages=[];scope=[]
def passage(p,start,end,label,kind='text'):
 rel=bind(p);b=(ROOT/rel).read_bytes()
 if kind=='text':
  lines=b.decode().splitlines(keepends=True);assert 1<=start<=end<=len(lines)
  part=''.join(lines[start-1:end]).encode();excerpt=''.join(lines[start-1:min(end,start+2)]).strip()
 else:part=b;excerpt='Visual read of entire rendered page; garbled extracted text not relied upon.'
 passages.append({'path':rel,'start':start,'end':end,'label':label,'kind':kind,'file_sha256':sha(b),'passage_sha256':sha(part),'opening':excerpt})
for r in pins:
 p=ROOT/r['local']
 if '/sections/' in str(p) or p.name in ('main.tex','paper.tex','README.md'):
  passage(p,1,len(p.read_text().splitlines()),'Complete G/D proof or containing document')
specs=[('adjacent-v1-pdf.txt',1,521,'Jiang–Xi complete v1 proof; Lemmas 2.1,5.1 and Corollary 6.1'),('progressions-v1.txt',1,640,'Burgin et al. complete v1; Question 1, Theorem 1.1, Proposition 3.3, structured Cantor conditions'),('chlebik-v1.txt',75,220,'Chlebik parameter-plane covering, Proposition 1 and Theorem 2'),('chlebik-v1.txt',587,626,'Chlebik projection-axis/exceptional-set interface'),('chlebik-v1.txt',705,880,'Chlebik Theorem 15 complete relative-gap argument'),('unbounded-primary.txt',55,212,'KP definitions and theorem statements'),('unbounded-primary.txt',353,740,'KP complete Sections 3 and 4 proofs, including moving index set and hyperplane partition')]
for name,a,b,label in specs:
 p=A/'literature'/name;end=min(b,len(p.read_text().splitlines()));passage(p,a,end,label)
for n in range(3,12):passage(A/'literature/kolountzakis-pages'/f'page-{n:02}.png',n,n,f'Kolountzakis 1997 original PDF page {n}; independent visual reading',kind='image')
for p in ['frontier/iterations/i36-harmonic-analysis-discovery.md','frontier/reviews/i36-common-geometric-avoidance-r2.md']+priors[:-1]:
 lines=(ROOT/p).read_text().splitlines()
 if 'i14-' in p:limits=[(1,min(len(lines),260))]
 elif 'i15-' in p:limits=[(52,120)]
 elif 'i30-' in p:limits=[(66,140)]
 else:limits=[(1,len(lines))]
 for lo,hi in limits:passage(p,lo,hi,'Proof/review gate comparison; detailed read scope below')
write('read-passages.json',passages)
mapping={'jiang-v1.pdf':'adjacent-v1-pdf.pdf','burgin-v1.pdf':'progressions-v1.pdf','chlebik-v1.pdf':'chlebik-v1.pdf','kp-published.pdf':'unbounded-primary.pdf','kolountzakis-1997.pdf':'kolountzakis-correct-primary.pdf'}
pdfmap=[]
for fresh,old in mapping.items():
 f=S/'literature'/fresh;o=A/'literature'/old;assert f.read_bytes()==o.read_bytes()
 pdfmap.append({'fresh':str(f.relative_to(ROOT)),'read_copy':bind(o),'sha256':sha(f.read_bytes()),'byte_identical':True})
write('primary-equivalence.json',pdfmap)
versions=[]
for p in sorted((S/'literature').glob('*current.html')):
 t=p.read_text();i=t.index('Submission history');j=t.find('Full-text links:',i)
 versions.append({'path':str(p.relative_to(ROOT)),'submission_history':re.sub(r'\s+',' ',re.sub('<[^>]+>',' ',t[i:j])).strip()})
write('versions.json',versions)
write('read-scope.json',{'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','complete_proof_reads':['G, every proof section','D, every proof section','Jiang–Xi 2610.11449v1 complete','Burgin et al. 2210.09284v1 complete','I36 author §§1–12 and full R2 report'],'selected_primary_reads':specs[2:],'visual_read':'Correct Kolountzakis author PDF pages 3–11, nine retained PNGs independently viewed; includes Theorems 1–3 and proofs §§2.1–2.4,3.1–3.3; not claiming complete §3.4 thereafter.','gate_reads':{'R011 and i25 review':'complete','I14':'decisive reduction §§1–6; exact local stability inequality and transfer','I15':'§§3.1–3.5 marked annulus recursive operation, lines52–120','I17':'§§3–4 decisive adjugate/product proof and verdict; supporting remainder inspected','I30':'lines66–140 Clarke/TW exact transfer','I02':'original full report and independent review'},'inventory':'All 749 manuscript paths, all 9340 cached text files searched and independently SHA/Git-blob checked; catalogue 719 lags. This is NOT semantic reading of all manuscripts.','unrelated_hits':'Other primary-name matches refer to Fourier/Hadamard positive-definite methods and lattice tilings in finite-cylinder approximation, not similarity avoidance. Broad common-geometric regex is deliberately noisy.','failures_and_exclusions':['No fresh direct HTTP retrieval failed (11/11 HTTP200).','Earlier unretained exploratory search is not used as sealed evidence; four later web query/response snapshots are retained.','Author historical guessed math/9603218 is Temme, excluded. Correct eigen-space.org/mk/ps/universal.pdf bytes match fresh download.','Historical nonexistent Burgin v2 and text-extraction failures retained in bound author records.','Withdrawn 2001.02395v2 excluded, not a proof dependency.','Survey currentv2 metadata checked only for orientation/version correction; no theorem justified by survey.','Rajchman, full-Hausdorff-dimension and twofold-sumset sources not audited as competing proofs: different hypotheses/pattern or measure conclusion; no novelty conclusion relies on their absence.'],'no_upstream_truth_audit':True,'contribution_scope':'A only; infinite omission is its tail corollary; no sideclaim promoted'})
write('input-manifest.json',inputs)
print(json.dumps({'bound_inputs':len(inputs),'pinned_files':len(pins),'read_passages':len(passages),'fresh_identical_primary_pdfs':len(pdfmap)}))
