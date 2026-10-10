#!/usr/bin/env python3
"""One-time evidence indexing; writes only the owned I49 source directory."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i49_hard_moment_quantitative_stability'
def save(name,value):(S/name).write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
notes=json.loads((S/'execution-notes.json').read_text())
if not any(x.get('failure')=='AssertionError: interval moment Hessian' for x in notes):
 notes.append({'kind':'diagnostic correction','failure':'AssertionError: interval moment Hessian',
 'cause':'The algebra-only zero helper does not reduce the hyperbolic identity sech^2=1-tanh^2. The unchanged expression passes SymPy simplify; this diagnostic now calls simplify explicitly. Original second script retained as diagnostic-development/check-v2.py. All prior polynomial assertions in that run had passed.'})
save('execution-notes.json',notes)
records=[]
(S/'passages').mkdir(exist_ok=True)
def passage(path,lo,hi,use):
 p=S/path;lines=p.read_bytes().splitlines(keepends=True)
 assert 1<=lo<=hi<=len(lines),(path,lo,hi,len(lines))
 b=b''.join(lines[lo-1:hi]);name=f'passages/{len(records):03d}.txt';(S/name).write_bytes(b)
 records.append({'source':path,'source_sha256':sha(p.read_bytes()),'first_line':lo,'last_line':hi,
 'extract':name,'sha256':sha(b),'use':use,'status':'actual text read; no claim to read other portions'})
primary={
 'centered-v2':[(720,835,'Moment convergence proof; quadratic-tilt extension checked in report'),
 (925,1095,'Unnormalized square completion and retained R and derivative terms'),
 (1290,1495,'Equality compactness and positive joint contact-pair boundary argument'),
 (1812,1833,'External proposed-proof status and references')],
 'bonnet':[(130,210,'W1 stability theorem hypotheses'),(701,945,'Restricted inverse, comparison, and coercivity proofs')],
 'berman':[(1,185,'Compact-target theorem hypotheses'),(1209,1302,'Existence, local regularity and uniqueness proof'),(1546,1586,'Interior Monge-Ampere regularity contract')],
 'cule':[(135,225,'Log-concave density convergence'),(240,328,'Proof of density convergence and tail control')],
 'figalli':[(45,75,'Interior Holder estimate statement'),(130,240,'Quantitative interior proof framework')],
 'klartag':[(1,115,'Hard convex target setting'),(1275,1385,'Hard Hessian cap and removal of boundary smoothness'),(1420,1530,'Moment spectral form and identities')],
 'hug-schneider':[(1,275,'BL support-measure continuity statement and parallel-volume proof')],
 'fmp':[(1,190,'Anisotropic deficit and asymmetry definitions, theorem'),(505,530,'Endpoint of proof outline'),(1396,1585,'Actual quantitative proof and affine normalization')],
 'bh':[(205,305,'Subspace cone-mass stability hypotheses')],
 'bd':[(255,350,'Reflection-dependent stability statements'),(625,735,'Coordinate-product grouping proof')],
 'lu':[(35,115,'Reflection theorem scope')],
 'xi':[(795,910,'Global zonoid equality theorem and proof')],
 'vanhandel':[(710,815,'Nonsmooth local zonoid equality proof')],
 'minkowski2026':[(1,37,'Current PDF version and authors'),(215,305,'Current quantitative Minkowski statements and p range')],
 'klr':[(100,130,'Local spectral setting'),(208,270,'Homogeneous strengthened Brascamp-Lieb implications'),(1830,1985,'Actual transport-Hessian Bochner proposition and proof')],
 'wang':[(220,254,'Projection and smooth-rigidity scope'),(759,821,'Actual segment-variation rigidity proof')],
 'he-liu':[(167,217,'Smooth-density uniqueness and strict spectral statements'),(498,585,'Actual common smooth-density rigidity proof')]
}
for name,items in primary.items():
 for lo,hi,use in items:passage(f'primary/{name}.txt',lo,hi,use)
base='pinned/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/'
for name in ['moment','identities','density','tensor','variance','reduction','measure']:
 path=base+name+'.tex';passage(path,1,len((S/path).read_bytes().splitlines()),'Actual full pinned proof operation or companion, accepted premise; measure/Lp is scope screening')
passage(base+'introduction.tex',1,100,'Pinned statement and scope')
passage(base+'introduction.tex',175,226,'Pinned proof-operation antecedents and companion attribution')
prior=[
 'frontier/iterations/i44-logarithmic-equality-polytopes.md',
 'frontier/iterations/i46-quantitative-logarithmic-stability.md',
 'frontier/reviews/i45-logarithmic-equality-r2.md',
 'frontier/reviews/i47-planar-logarithmic-stability-r2.md',
 'frontier/reviews/i48-planar-logarithmic-stability-novelty.md']
for name in prior:
 path='frozen/'+name;passage(path,1,len((S/path).read_bytes().splitlines()),'Prior report/review read in chunks; original disposition and objections retained')
save('read-passages.json',records)
versions=[]
for p in sorted((S/'primary').glob('*.txt')):
 header=p.read_text()[:18000]
 versions.append({'file':str(p.relative_to(S)),'sha256':sha(p.read_bytes()),
 'arxiv_header':re.findall(r'arXiv:\S+\s+\[[^\]]+\][^\n]*',header),
 'authority':'Fresh downloaded PDF text; author-hosted PDFs without version header are identified by URL and hash.'})
for p in sorted((S/'primary').glob('*current.html')):
 text=p.read_text()
 lines=[q for q in text.splitlines() if any(x in q for x in ['citation_arxiv_id','citation_date','Submission history','[v1]','[v2]','[v3]'])]
 versions.append({'file':str(p.relative_to(S)),'sha256':sha(p.read_bytes()),'version_lines':lines})
save('versions.json',versions)
save('source-contracts.json',[
 {'source':'Pinned logarithmic manuscript, full selected operation passages','status':'accepted premise by user',
 'use':'Finite-slab concavity, smooth moment coordinates, compact adjunction, dense even range, invariant tensor identity; retain remainders rather than normalized leading variance.',
 'not_used':'No catalogue summary or assertion that an unbounded soft target has a radius-only Hessian cap.'},
 {'source':'Liu–Sun–Xiong 2610.10152v2','status':'attributed mechanism, not assumed external theorem',
 'use':'Actual completion algebra and equality compactness/contact mechanism checked against pinned identities. I49 independently proves fixed-defect weak-field passage and its quantitative geometric interfaces.',
 'not_used':'Centered nonsymmetric theorem; equality weak compactness as a claimed quantitative rate.'},
 {'source':'Bonnet–Rubinstein; Berman–Berndtsson; Cule–Samworth; Figalli–Jhaveri–Mooney',
 'status':'Classical/current primary theorems with hypotheses checked in report §3.2',
 'use':'Fixed-budget existence of local Ck moment coefficient convergence. No convergence rate enters final exponent.'},
 {'source':'Klartag','status':'Hard convex-target cap only',
 'use':'After passage: bounded gradient image, Hessian upper bound, determinant lower bound, exponential tails with dimensional exponent after John normalization.'},
 {'source':'Hug–Schneider','status':'Classical quantitative support-measure continuity',
 'use':'BL continuity with exponent 1/2; direct gauge proof also supplied. No total-variation convergence.'},
 {'source':'Figalli–Maggi–Pratelli','status':'Classical quantitative anisotropic isoperimetry',
 'use':'Mixed volume plus volume yields Fraenkel asymmetry; symmetry removes translation; cap estimate yields Hausdorff. All interfaces proved in §8.2.'},
 {'source':'Kolesnikov–Livshyts–Rotem 2507.12099v3; Wang 2510.19061v2; He–Liu 2510.21530v1',
 'status':'Actual companion operations and restricted equality proofs read',
 'use':'Credit transport-Hessian Bochner identity, homogeneous variance equivalence, smooth segment-variation rigidity and positive smooth-density uniqueness. Their smoothness/pinching constants do not supply the unrestricted target rate.'},
 {'source':'Böröczky–De; Böröczky–Henk; Lu; Xi; van Handel; Böröczky–Machado–Ramos',
 'status':'Scope screening using actual stated hypotheses and selected proofs',
 'use':'Existing reflection, cone-mass, zonoid, classical and p>1 theories credited. No claim of exhaustive worldwide priority.'}
])
responses=json.loads((S/'responses.json').read_text())
save('network-summary.json',{'responses':len(responses),'successes':sum(r['ok'] for r in responses),'failures':sum(not r['ok'] for r in responses),
 'note':'Initial 19 requests and four supplemental companion requests all returned HTTP 200. Search result captures are ancillary and not proof premises. PDF derived text is replayed by verify.py. Older failed responses remain only in unchanged prior archives.'})
print(json.dumps({'read_records':len(records),'version_records':len(versions)}))
