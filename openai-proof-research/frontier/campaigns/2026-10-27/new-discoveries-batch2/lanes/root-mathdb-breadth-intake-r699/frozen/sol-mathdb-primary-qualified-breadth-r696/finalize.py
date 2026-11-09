import json,pathlib,hashlib,tempfile,subprocess,datetime
O=pathlib.Path(__file__).resolve().parent;L=O.parent
load=lambda p:json.loads(p.read_text())
def write(n,d):(O/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def entry(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
flat=load(O/'flat-bindings.json');p=L/'sol-mathdb-primary-qualified-breadth-r642/failures.md'
if p.exists():
 e=entry(p);flat.append(e);write('flat-bindings.json',flat);assert entry(p)==e
 print('r642 stopped failures',p.read_text()[:3500])
f=load(O/'failures.json');f['stopped_routes_preserved']+=['r578 https://arxiv.org/html/2207.02920v2 HTTP404','r578 https://math.torontomu.ca/~pralat/papers/2024_Erdos_Gyarfas.pdf TLS','r578 https://people.math.rochester.edu/faculty/doug/otherpapers/Christensen-Hovey.pdf timeout','r684 https://arxiv.org/html/2201.12415v2 HTTP404','r684 https://arxiv.org/pdf/2201.12415v2 HTTP404'];f['deviations']+=['Initial assigned-record full-metadata print truncated; all50 exact statements subsequently read in two bounded batches. No adjacent unassigned statement displayed.','Primary page10 inspected visually after binding rendered PNG; adjacent source material not treated as a reviewed target.'];write('failures.json',f)
# Independent payload checker tests on tiny synthetic fixtures: no original is mutated/copied.
neg=[]
with tempfile.TemporaryDirectory(prefix='negative-fixture-',dir=O) as tmp:
 root=pathlib.Path(tmp);p=root/'a';p.write_bytes(b'abc')
 base={'path':'a','size':3,'sha256':hashlib.sha256(b'abc').hexdigest()}
 def run(label,e,extra=False):
  (root/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[e]}))
  if extra:(root/'unexpected').write_text('x')
  r=subprocess.run(['python3','-B',str(O/'verify.py'),'--payload-only',str(root)],capture_output=True,text=True)
  if extra:(root/'unexpected').unlink()
  neg.append({'test':label,'exit':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()});return r.returncode
 assert run('positive_control',base)==0
 assert run('wrong_hash_same_size',{**base,'sha256':'0'*64})!=0
 assert run('wrong_size',{**base,'size':4})!=0
 assert run('extra_file',base,True)!=0
write('negative-tests.json',neg)
s=load(O/'source-coverage.json');counts=s['classification_counts']
(O/'SUMMARY.md').write_text('''# r696 independent breadth screening

Exactly 50 assigned literal records reviewed; no replacements. Classification: 17 complete, 19 definition-dependent, 7 scope-ambiguous, 7 incomplete. Every row retains its exact UTF-8 statement, canonical record hash, chunk/line, quantifiers, classification reason and individual technical disposition.

Zero hypothesis briefs; zero discovery credit. Counts remain 9 additional / 39 total / next 40. Baseline 8,283 is reported literal reviews, not full technical corpus coverage. These 50 distinct assigned reviews may bring reconciled literal review coverage to 8,333; root alone integrates. The 10,000 routing rows remain metadata only.

Two selected primary passages inspected: arXiv:1011.4658v1 states the n=4 exception refuting literal 320721; arXiv:1303.6651v1 Conjecture2.11 contains the unconstrained p_(s+1) defect in literal325243. Exact integer check s=1, q=qtilde=1, p=(0,0,1) gives hypothesis sums (0,0,0) but violates p2=0. This is a wording correction, not an eligible result. Source page10 visually checked after image binding. No repaired conjecture promoted. No whole-source, full-dependency, successor-body or current-registry clearance claimed.

Integrity: independently checked exact intake payload and direct original/copy pairs without executing upstream verification; all 20 original r301 chunks and eight separately listed frozen inputs checked in place against its intake-bound manifest. Assigned queue equals reservation; all three fifty-ID sets disjoint from 8,283 baseline and protected IDs. r694 and HELD r628 preserved. r304 exclusions, historical dispositions and r363 Cayley decision checked; r695 adjudications retained, including retired338290/339564/372627 and parked337963. 338366 remains excluded with text/figure reconstruction and unread-journal limitations.

Access: two generic-header public arXiv PDF requests, no failures; bytes bound before extraction, derivatives before reading. Zero MathDB requests. All inherited stopped routes preserved, including r578, r642 Gorenstein TLS, r684 v2 404s, OEIS403 and OUP403. Current registry unavailable: HOLD. No absence-of-hits inference. No shared-file/git/Lean/manuscript/credit changes.

Re-run `./verify.sh` to check originals, exact payload, reservations and literal hashes read-only under the fixed 512MiB/210CPU-second/230wall-second guard. Negative tests reject wrong hash, wrong size and extra file on bounded synthetic fixtures. Manifest excludes only itself and final-verification-receipt.json. Integrity PASS is neither mathematical nor novelty PASS. See failures.json for retained deviations and flat-bindings.json for immutable references.
''')
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  e=entry(p);e['path']=str(p.relative_to(O));files.append(e)
write('manifest.json',{'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files})
print('manifest',entry(O/'manifest.json'))
