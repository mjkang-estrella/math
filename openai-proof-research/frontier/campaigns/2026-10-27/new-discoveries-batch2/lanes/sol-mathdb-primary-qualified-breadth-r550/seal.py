from pathlib import Path
import json,hashlib,datetime,subprocess,sys,collections
D=Path(__file__).resolve().parent;L=D.parent
flat=json.loads((D/'flat-bindings.json').read_text())
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'AGENTS.md',next(x for x in D.parents if x.name=='openai-proof-research')/'AGENTS.md']:
 b=p.read_bytes();flat.append(dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(D/'flat-bindings.json').write_text(json.dumps(flat,indent=2)+'\n')
ds=json.loads((D/'dispositions.json').read_text());counts=dict(collections.Counter(x['disposition'] for x in ds))
(D/'SUMMARY.md').write_text('''# Assigned breadth screening r550

50/50 assigned literal statements technically read; exact UTF-8 and canonical normalized-record hashes, original chunk and one-based line attached individually. Baseline: 4,683 reported reconciled literal reviews. This lane offers 50 disjoint additional literal reviews for root reconciliation (arithmetic total 4,733); no shared ledger/index edits and no claim of full-corpus technical coverage.

Proposals: **0**. Accepted credit: **0**. Campaign remains 9 additional /39 total /next40. Four selected primary passages plus adjacent definitions/results read; zero whole-source, successor-body or full-dependency audits. Individual dispositions explain the quantified scope and concrete obstruction. Explicit known-result reports are screened out without pretending their proof bodies were audited. All other unresolved mathematical/prior/source gates remain HOLD/PARK, including the unavailable current proof registry.

Integrity: intake exact payload and all direct original/copy pairs checked independently without executing upstream verify.py; all 20 original r301 chunks and eight frozen inputs hash/size checked in place. Three sets of fifty are disjoint from each other, 4,683 coverage IDs, and protected IDs. r304 and r363 exclusions and current adjudications preserved. Flat references only; no historical-tree or corpus copies. The manifest covers every lane file except itself and the named final receipt, including the verifier. Bounded fixture tests reject a same-size hash change, size change and extra file. Final receipt records manifest SHA256 and size.

Access: zero MathDB requests. Eight allowed primary fetches succeeded. All parked routes preserved. No mathematical finite sweep or new certificate, no Lean/manuscript/credit changes. Source limits, stopped routes and process deviations are in source-coverage.md and failures.md.

Run independent read-only verification from any directory:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B '''+str(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')+' python3 -B '+str(D/'verify.py')+'''
```

Integrity PASS is not mathematical validity or novelty PASS.

Disposition counts: '''+json.dumps(counts,sort_keys=True)+'\n')
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  b=p.read_bytes();files.append(dict(path=str(p.relative_to(D)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(D/'manifest.json').write_text(json.dumps(dict(files=files,excluded_exact_paths=['manifest.json','final-verification-receipt.json']),indent=2)+'\n')
r=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True)
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr,manifest_sha256=hashlib.sha256((D/'manifest.json').read_bytes()).hexdigest(),manifest_size=(D/'manifest.json').stat().st_size,scope='integrity only; no math/novelty acceptance')
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(r.returncode)
