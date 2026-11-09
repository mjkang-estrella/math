import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
failures=[
 {'kind':'scientific','route':'positive kernel powers','failure':'Schur gives integer powers; arbitrary powers fail for PSD matrices, and no admissible homogeneous singular metric was constructed.'},
 {'kind':'scientific','route':'fixed Jacobi integrals','failure':'112 parameter cases and64 modes are finite, uncertified numerics; no all-mode or all-exponent monotonicity proof.'},
 {'kind':'source-scope','failure':'UP24 does not define equivalent distance or explicitly state invariance; no permissive interpretation adopted as outcome.'},
 {'kind':'numerical-diagnostic','failure':'First unnormalized512/1024 run had max absolute discrepancy2904.29833984375; replaced representation by positive normalization, final discrepancy9.189180827373633e-8. Neither run supplies rigorous error bounds.'},
 {'kind':'retrieval-identification','url':'https://mathdb.org','failure':'Unrelated Korean site; zero proof-registry or current-head evidence.'},
 {'kind':'history-screen','failure':'Initial rg path inventory included historical copied reports. Corrected canonical direct-lane filter; compact hash-deduplicated frozen files retained. No recursive directory copying.'},
 {'kind':'bounded-prior','failure':'No current proof-registry head; forbidden GitHub endpoints not retried. Breadth original partial-result proof bodies unread.'},
 {'kind':'read-locator','failure':'Exact phrase Proof of Theorem3.1 absent in predecessor. Read actual section3 Lemma3.1/Proposition3.2 proof instead.'}
]
(L/'failures.json').write_text(json.dumps(failures,indent=2)+'\n')
(L/'run-instructions.txt').write_text('Run from any directory, replacing L with this absolute lane path.\nG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py\nOPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python "$G" python "$L/checks.py"\nAfter intentional file changes, regenerate manifest then verify:\nOPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python "$G" python "$L/finalize.py"\nOPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python "$G" python "$L/verify.py"\nDo not rerun source retrieval merely to reproduce numerics. Frozen PDF text can be regenerated using exact pdftotext commands in text-bindings.json.\n')
files={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
(L/'final-manifest.json').write_text(json.dumps({'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'algorithm':'sha256','excludes':['final-manifest.json','verification-receipt.json'],'files':files},indent=2)+'\n')
print({'manifest_files':len(files)})
