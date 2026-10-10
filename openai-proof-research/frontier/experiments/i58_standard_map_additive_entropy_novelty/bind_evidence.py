from pathlib import Path
import hashlib,json,re,html
from html.parser import HTMLParser
S=Path('frontier/sources/i58_standard_map_additive_entropy_novelty')
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
class TextParser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','h1','h2','h3','li','div']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
htmls=[]
for p in sorted((S/'literature').glob('*.html')):
 t=TextParser();t.feed(p.read_text());b=('\n'.join(re.sub(r'\s+',' ',x).strip() for x in ''.join(t.out).split('\n') if x.strip())+'\n').encode();q=p.with_suffix('.readable.txt');q.write_bytes(b);htmls.append({'html':str(p.relative_to(S)),'text':str(q.relative_to(S)),'sha256':sha(b)})
dump(S/'html-extractions.json',htmls)
base='pinned/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/build/sections/'
contracts=[]
specs=[('introduction',['main:map','main:pesin'],'Exact family, area and nonergodic entropy integral; not headline positivity alone.'),('setup',['setup:norm-bounds','scale:distance-deficit','setup:shortfall-count'],'Uniform determinant-one bounds, stationarity, exact constant 4 shortfall count.'),('cancellation',['can:theorem','can:local-scarcity','can:eta-choice'],'Fixed structural constants; matched-scale scarcity is inherited, not quantitative invariant small ball.'),('local-scarcity',['loc:green','loc:inverse-chains','loc:boundary-fourth'],'Actual inverse differentiation precedent; qualitative scarcity constants need not have an effective modulus.'),('bridge',['bridge:theorem','bridge:graphs','bridge:direction-step','bridge:green','bridge:determinant-distortion','bridge:label-jacobian'],'Fixed observations and thresholds, prefix eligibility, varied inverse, full extended leaf, real area Jacobian.'),('scales',['scale:doubling','scale:long-deficit','scale:selection','scale:local-mass','scale:limits','scale:decomposition'],'Only crossing existence uses long deficit; all downstream shifted-data and floor contracts retained.'),('geometry',['shape:exclusions','shape:classification','end:balance','end:terminal','end:remainder'],'Fixed-test weighted exclusions, no escaped affine mass, strict loss at one limit and nonpositive remainder.')]
passages=[]
def bind(path,start=1,end=None,reason='',anchors=None):
 p=S/path;b=p.read_bytes();ls=b.decode().split('\n');end=end or len(ls);part=('\n'.join(ls[start-1:end])+'\n').encode();passages.append({'path':path,'start':start,'end':end,'line_convention':'split on literal LF, 1-based inclusive','sha256':sha(b),'passage_sha256':sha(part),'reason':reason,'anchors':anchors or []})
for n,labels,reason in specs:
 path=base+n+'.tex';b=(S/path).read_bytes();contracts.append({'path':path,'sha256':sha(b),'labels':labels,'applicability':reason,'truth_assumed':True,'upstream_truth_audited':False});bind(path,reason='Entire mathematical section read: '+reason,anchors=['\\label{'+x+'}' for x in labels])
for name in ['i52-ergodic-dynamical-discovery.md','i54-standard-map-additive-entropy.md']:
 bind('inputs/frontier/iterations/'+name,reason='Entire original report, not amended')
bind('inputs/frontier/reviews/i57-standard-map-additive-entropy-r2.md',reason='Entire completed proof audit read after explicit dependency update')
for name,lo,hi,reason in [
 ('knill-v2',1,113,'Withdrawal, Conjecture 1.1, one-step upper and explicit normalization'),
 ('bxy-v1',110,205,'Actual Theorems 1-3 and standard-map specialization, positive noise cutoffs'),
 ('bxy-v1',290,327,'Stationary projective integral interface'),
 ('bxy-v1',396,655,'Transition density, Lemmas 9-10, Proposition 11 and noise-dependent balancing'),
 ('blumenthal-v1',155,255,'Increasing-parameter Theorems A-C and finite-time Theorem D'),
 ('blumenthal-v1',880,960,'Proposition 3.4 and finite-time specialization proof'),
 ('ap-v1',1715,1795,'AP statement and projective contraction proof hypotheses'),
 ('ap-v1',1919,1960,'Practical AP gaps/angles and proof conversion'),
 ('ldt-v2',220,340,'Definitions 1.5-1.7 and Theorem 1.1 hypotheses and proof architecture'),
 ('bcs-v1',80,120,'Theorem A and Corollary 1.1'),
 ('bcs-v1',2629,2665,'General Theorem D bounded smooth-map convergence restriction'),
 ('bloor-v1',520,565,'Critical-strip cone hypothesis and conditional expansion'),
 ('holland-v1',235,273,'Summability/domain hypotheses and Main Theorem')]:bind('literature/'+name+'.txt',lo,hi,reason)
for n in ['knill-current','bxy-current','blumenthal-current','ap-current','ldt-current','bcs-current','bloor-current','holland-current']:
 p='literature/'+n+'.readable.txt';ls=(S/p).read_text().split('\n');i=next(i for i,x in enumerate(ls) if 'Submission history' in x);bind(p,i+1,min(len(ls),i+14),'Observed current arXiv version history')
bind('literature/knill-2026-response.readable.txt',reason='Current author status; not an asserted theorem or proof')
dump(S/'passages.json',passages);dump(S/'source-contracts.json',contracts)
dump(S/'search-assessment.json',{'inventory':'749 manuscript directories, all 9340 ignored text files matched to complete tree blobs','standard_map':'The dynamical matches are confined to one master. Algebraic uses of standard map and generic Kolmogorov-Sinai mentions excluded by actual context. No additive companion found.','projective':'1833 broad hits; relevant varied Green, derivative-chain, finite graph and coarea mechanisms read in full actual master. Generic PDE Green functions and probability small-ball estimates not automatically transferred.','entropy':'255 broad hits; no second exact fixed-parameter area additive theorem identified. Absence of a duplicate is not the significance argument.','decision':'Technical by explicit source-operation plus elementary seed reduction, not duplicate by search absence.'})
(S/'objections-and-responses.txt').write_text('''I58 independent objections and disposition.
1. H improves only the headline positivity theorem? Rejected framing: compare all source operations. Relative-seed lemma proves d=O(e_n0+1/n0).
2. Does I52 S alone prove H? No. S has no rate. Elementary F pays a prescribed growing seed; fixed-threshold SC supplies amplification exclusion.
3. Is the parameter-dependent crossing also a moving bridge threshold? No. Bridge observations remain fixed; theta only selects scales.
4. Must terminal loss be uniformly bounded below? No. Negation of bounded B gives one forbidden exact limit, with its own strict loss.
5. Could SC extraction be the indispensable new substantial mechanism? I52 already exposes identical postselection sufficiency; no new downstream operation is supplied in I54.
6. Could G be substantial independently? Its actual restricted claim reduces to varied inverse differentiation, source label Jacobians, monotonicity and summable direction estimates. Open complement is not credited.
7. Does mass control close H via feedback? No; coefficient is 200 and resulting B<=O(1)+400B is non-closing. O(1/log K) mass comes after H.
8. Exact external duplicate? Not established. Verdict TECHNICAL ONLY, not DUPLICATE or world-priority certification.
9. User dependency update: I57 PASS ORIGINAL WITHOUT REPAIRS now satisfies initial correctness condition. Independent significance reduction was already written and remains unchanged.
10. Historical I52 vanilla verifier failure is retained, with exactly 12 added I54 lines/no removals; separate diagnostics and unchanged seals do not relabel that run PASS.
''')
print({'contracts':len(contracts),'passages':len(passages),'html_extractions':len(htmls)})
