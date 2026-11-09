import pathlib,json,hashlib,subprocess,datetime
O=pathlib.Path(__file__).resolve().parent;L=O.parent
# Corrections made before final manifest.
p=O/'dispositions.json';rows=json.loads(p.read_text())
for x in rows:
 if x['mathdb_id']==360120:
  x['disposition']='HOLD_POSITIVE_MATCHING';x['technical_review']='All 3-uniform H are quantified. Positive matching requires a source-defined strict weight-separation condition; partitioning into ordinary matchings does not suffice. No universal construction meeting the exact quadratic bound established; no small-domain contradiction claimed.'
 if x['mathdb_id']==359807:x['technical_review']+=' Required bound r304 historical disposition explicitly records unresolved radial-monotonicity failure and a multiple-maximizer gap, with journal body unread. Preserve those objections; no reopening or clearance here.'
p.write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(O/'SUMMARY.md').write_text('''# r516 breadth screening — zero proposals

Read all 50 assigned literal full statements, with exact UTF-8 statements, corpus chunk/line, statement SHA256 and canonical-record SHA256 retained in dispositions.json. These are record-statement reviews, not complete technical corpus coverage. Five primary PDFs received selected question/definition or proof passage review; one closest successor received selected body review. Only the star-critical Ramsey PDF was read across its entire extracted body; external dependencies were not independently replayed.

Intake r515 exact payload, every direct original/copy binding (including intentional original=copy tags), original r301 manifest, all 20 original chunks and all eight inventory frozen_inputs independently verified in place. No upstream verifier executed, no corpus copied. All three reservation sets are mutually disjoint and avoid protected IDs and the 3,933 reported-review baseline. This lane reports 50 additional literal reviews; root alone may reconcile a 3,983 total. The 6,000 metadata routing rows earn no scientific review credit. Counts remain 9 additional / 39 total / next 40.

No hypothesis brief qualifies: proposals.json is empty. 359499 is already refuted by source Theorem 1.4 and its local proof. 360358 confuses the minimum isolation number with maximum cycle packing. 361256/361257 are the same conjectural scope, separately read as records. 359807 retains the r304 unresolved radial-monotonicity and multiple-maximizer objections. r304 exclusions/historical dispositions, r363 Cayley rejection, and current r515 adjudications remain unchanged. No promotion of any protected or sibling-batch target.

359606: executed exact GF(2) checks for all 63 monic constant-one polynomials of degrees 1–6 and all permitted m, 158 cases, no mismatch. A possible Cartier/simple-pole descent route has unproved contraction/descent and routine-subsumption obligations. This is parameter evidence, not a proof or novelty PASS.

360292: source correct coloring requires exactly two colors on each triple. A 35-variable finite MILP probe using all 877 set partitions aborted SIGABRT before producing any result (guard CPU/memory/wall caps unchanged). No retry, exhaustive-search claim or unsatisfiability certificate. 361172: the source disjoint-disk mechanism does not reach all six-point configurations; selected successor proof concerns an upper bound, not the required lower bound.

All six PDFs were lawfully fetched from public arXiv endpoints; request URL, resolved URL, response headers, UTC, byte hashes, extracted-text hashes, exact versions and candid passage coverage are in source-provenance.json. PDF bytes were bound before extraction, derivatives before reading. No visual/layout verification or whole-body proof clearance is claimed for selected passages. No direct MathDB request or prohibited route was used. Search snippets were leads only; incidental registry snippets were not opened. Current proof registry unavailable means HOLD. No inference of novelty from missing hits, tags, status or solution arrays.

Failures and deviations are retained in failures.json: prebinding administrative/schema inspection exposed a short ledger excerpt and reservation metadata; later matching hashes do not repair its timing. The finite exploratory probe preceded establishing a closest successor body for that exact target and was stopped after its abort. No Lean, manuscript, credit, shared ledger, sibling or upstream edits; no git or children.

Run the independent read-only verifier with:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B verify.py
```

Run from this lane. Default verification reads actual originals and checks exact manifest payload, all bindings, 20 chunks, eight inputs, reservation disjointness, all 50 literal/canonical hashes and source byte bindings. Nonzero exit signals a mismatch. Bounded synthetic negative tests reject changed hash, size and extra files without mutating originals. Integrity PASS is independent of mathematics, source scope, dependency, registry and novelty gates, which remain uncleared. Manifest excludes only itself and the named final-verification-receipt.json; that separate receipt binds manifest SHA256 and size.
''')
# Preserve actual negative execution as subprocess exits, independently from originals.
script=O/'verify.py';s=script.read_text();s=s.replace('try:main()',"try:\n  if len(sys.argv)==3 and sys.argv[1]=='--payload-root':payload(pathlib.Path(sys.argv[2]));print('PASS_PAYLOAD_ONLY')\n  else:main()")
script.write_text(s)
neg=O/'negative_tests.py';neg.write_text('''import tempfile,pathlib,json,hashlib,subprocess,sys
O=pathlib.Path(__file__).resolve().parent
results=[]
with tempfile.TemporaryDirectory(dir=O,prefix='negative-fixture-') as tmp:
 p=pathlib.Path(tmp);b=b'abc';(p/'sample').write_bytes(b)
 m={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[{'path':'sample','size':3,'sha256':hashlib.sha256(b).hexdigest()}]}
 (p/'manifest.json').write_text(json.dumps(m))
 def run():return subprocess.run([sys.executable,'-B',str(O/'verify.py'),'--payload-root',str(p)],capture_output=True,text=True)
 assert run().returncode==0
 for kind,data in [('hash',b'abd'),('size',b'abcd'),('extra_file',b'abc')]:
  (p/'sample').write_bytes(data)
  if kind=='extra_file':(p/'unexpected').write_bytes(b'x')
  r=run();assert r.returncode!=0,(kind,r.stdout)
  results.append({'mutation':kind,'exit_code':r.returncode,'stderr':r.stderr.strip(),'rejected':True})
(O/'negative-tests.json').write_text(json.dumps({'originals_mutated':False,'bounded_fixture_tests':results},indent=2)+'\\n');print(json.dumps(results))
''')
subprocess.run(['python3','-B',str(neg)],check=True)
# This script itself is included; final receipt is the only excluded output besides manifest.
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(O/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},indent=2)+'\n')
r=subprocess.run(['python3','-B',str(script)],capture_output=True,text=True)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'scope':'Integrity only; no mathematics/novelty acceptance','guard':'fixed helper_guard.py enclosing this entire finalization process; 512MiB AS/groupRSS CPU210 wall230 unchanged'}
b=(O/'manifest.json').read_bytes();receipt['manifest_sha256']=hashlib.sha256(b).hexdigest();receipt['manifest_size']=len(b)
(O/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt));assert r.returncode==0
