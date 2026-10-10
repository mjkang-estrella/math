"""Create I60 evidence records once; not the read-only replay verifier."""
from pathlib import Path
import json,hashlib,re,platform,sys
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i60_threshold_structural_combinatorics_discovery'
if (S/'read-passages.json').exists():raise SystemExit('Evidence already exists; refusing to refresh.')
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(name,obj): (S/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
# Whole files are read ranges only when their complete substantive text was read.
passages=[]
def add(rel,lo,hi,purpose):
 p=ROOT/rel;lines=p.read_text().splitlines(keepends=True);hi=min(hi,len(lines));b=''.join(lines[lo-1:hi]).encode()
 passages.append(dict(file=rel,start=lo,end=hi,sha256=sha(b),purpose=purpose))
manifest=json.loads((S/'pinned-manifest.json').read_text())
for r in manifest:
 p=r['path'];f=r['frozen']
 if p.endswith('.tex') and ('/sections/' in p or p.endswith(('/introduction.tex','/fourier.tex','/restriction.tex','/completion.tex'))) and '/figures/' not in p:
  add(f,1,100000,'Full theorem/proof read; source dependency or strongest-companion comparison')
 elif 'Graph-Decompositions' in p and p.endswith('/main.tex'):
  add(f,1,100000,'Complete proof: same-parameter cover, compression/Hall, direct embeddings, fixed partition')
# Precise primary statement and proof passages inspected.
prefix='frontier/sources/i60_threshold_structural_combinatorics_discovery/literature/'
for name,lo,hi,purpose in [
 ('filmus-basis-pdf.txt',619,737,'Theorems 4.1/4.2: slice basis and harmonic lifting, not Boolean extension'),
 ('filmus-basis-pdf.txt',785,798,'Transposition influence normalization'),
 ('filmus-basis-pdf.txt',1070,1155,'Lemmas 5.5/5.6 and eigenvalue proof of Poincare'),
 ('filmus-mossel-pdf.txt',1065,1195,'Lemma 4.4 proof and Theorem 4.6: coupling/harmonic invariance comparison'),
 ('ahpt-pdf.txt',177,255,'Theorems 1.8/1.10--1.13 exact scopes'),
 ('ahpt-pdf.txt',270,425,'Deterministic-family permutation proof, not common random-host embedding'),
 ('ahpt-pdf.txt',980,1125,'Theorem 1.13 proof and Section 8 questions'),
 ('li-pdf.txt',90,184,'Current v2 statements, particularly Theorems 1.15 and 1.19'),
 ('li-pdf.txt',275,435,'Signed kernel proof, fractional density threshold'),
 ('park-pdf.txt',223,283,'Fractional and integral two-union comparison with density loss')]:add(prefix+name,lo,hi,purpose)
dump('read-passages.json',passages)
# Store theorem blocks (all selected files, claims of reading controlled above).
contracts=[]
for r in manifest:
 if not r['path'].endswith('.tex'):continue
 lines=(ROOT/r['frozen']).read_text().splitlines(keepends=True);txt=''.join(lines)
 for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}[\s\S]*?\\end\{\1\}',txt):
  lo=txt[:m.start()].count('\n')+1;hi=txt[:m.end()].count('\n')+1
  contracts.append(dict(file=r['frozen'],start=lo,end=hi,sha256=sha(''.join(lines[lo-1:hi]).encode()),text=m.group()))
dump('source-contracts.json',contracts)
watch=[
'frontier/sources/i52_ergodic_dynamical_discovery/seal.json',
'frontier/sources/i53_sharp_entropy_stability_discovery/seal.json',
'frontier/sources/i54_standard_map_additive_entropy/seal.json',
'frontier/sources/i56_sharp_entropy_stability_novelty/seal.json',
'frontier/sources/i58_standard_map_additive_entropy_novelty/seal.json',
'frontier/experiments/i57_standard_map_additive_entropy_r2/i52-direct-replay-failure.json',
'frontier/experiments/i52_ergodic_dynamical_discovery/verify.py']
dump('old-files-watch.json',[dict(path=p,sha256=sha((ROOT/p).read_bytes())) for p in watch])
dump('environment.json',dict(python=sys.version,platform=platform.platform(),byteorder=sys.byteorder))
# Version evidence and explicit failure records, not a stale abstract treated as a theorem.
versions=[]
for p in sorted((S/'literature').glob('*abs.html')):
 t=p.read_text();start=t.find('Submission history');excerpt=re.sub('<[^>]+>',' ',t[start:start+2200])
 versions.append(dict(file=str(p.relative_to(ROOT)),versions=re.findall(r'\[v\d+\]',excerpt),history=excerpt,withdrawn='This paper has been withdrawn' in t))
dump('literature/versions.json',versions)
dump('objections.json',[
 {'objection':'Cube total influence is not a spectral gap or universal noise-sensitivity theorem.','response':'T uses level-set coarea with L1 gradients only; no real-valued L2 spectral claim.'},
 {'objection':'Fixed-cardinality conditioning loses product symmetry/independence.','response':'The completion extension is equivariant under every coordinate permutation; every layer has the same mean; (3.4)--(3.9) pay the precise transference losses.'},
 {'objection':'A uniform swap-energy statement for all m might be stronger.','response':'Refuted by the exact invariant m=2 wedge ratio tending to 1/4.'},
 {'objection':'Priority bits allow direct reuse of simple-graph capture.','response':'Five bit coordinates on one edge have zero capture probability for k=4 despite support size below k^2/2.'},
 {'objection':'Piece embeddings or fixed roots might already glue.','response':'Full global injectivity would imply a false constant expectation-threshold comparison for spanning matchings; fixed-Y cut embedding is already in source proof.'},
 {'objection':'Hall slack implies local edge resilience.','response':'It gives only the stated candidate-vertex deletion partial; killing a rooted common neighborhood refutes the proposed local edge norm.'},
 {'objection':'A new fractional two-union inequality could be a discovery.','response':'Its exact threshold is already Li v2 Theorem 1.15; explicit weights are a two-row instance of source signed operations.'},
 {'objection':'Integral--fractional comparison settles same-p two unions.','response':'It loses density; the existing color-product mean and bin-power arguments do not pay same-p rounding.'},
 {'objection':'Yang search abstract supplies a current decomposition theorem.','response':'Official v2 is withdrawn; current PDF 404 retained. Not used.'},
 {'objection':'New endpoint exponent on a slice is substantial.','response':'Complete explicit reduction via classical Poincare, conditional expectations and coarea classifies it technical under I56/I58 standard.'},
 {'objection':'Growing prior reports can break old evidence reproduction.','response':'Four live ledgers informational; prior-screen domain is four frozen reports with line multisets. Old watched seals/failed-verifier evidence stay unchanged.'}
])
dump('literature/search-log.json',dict(initial_queries=[
'Ascoli He Park Talagrand graph expectation threshold decompositions 2026',
'sharp threshold graph properties slice G n m influences log squared',
'Talagrand discrete convexity conjecture fractional expectation threshold 2026',
'Boolean slice graph properties influence inequality vertex permutation invariant slice Bourgain Kalai',
'Filmus Wimmer KKL slice sharp threshold influence graph properties'],
initial_raw='Initial raw web responses remain in task transcript; not independently archived as files. Later raw searches are search-slice.json and search-final.json.',
mathdb='Homepage mathdb.org returned a Korean mathematics site; no relevant catalogue entry verified. No significance score assigned.',
local_parser_failure='Optional bs4 import failed (ModuleNotFoundError); no installation attempted. Title/version extraction used the Python standard library instead.'))
print(json.dumps(dict(passages=len(passages),source_contracts=len(contracts),watched=len(watch))))
