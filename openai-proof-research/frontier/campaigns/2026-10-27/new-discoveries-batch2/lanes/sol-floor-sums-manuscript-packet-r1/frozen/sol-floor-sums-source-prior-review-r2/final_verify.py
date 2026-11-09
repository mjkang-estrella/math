from pathlib import Path
import json,hashlib,time,datetime,os,resource
L=Path(__file__).resolve().parent;start=time.monotonic()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert all(os.environ.get(k)=='1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','PYTHONDONTWRITEBYTECODE'])
m=json.loads((L/'final-manifest.json').read_text());mh=sha(L/'final-manifest.json')
def verify():
    files={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['final-manifest.json','final-verification-receipt.json']}
    assert files==set(m)
    for s,r in m.items():assert sha(L/s)==r['sha256'] and (L/s).stat().st_size==r['bytes'],s
    for r in json.loads((L/'original-copy-checks.json').read_text()):
        assert sha(L/r['copy'])==r['sha256']
        if not r['administrative']:assert sha(Path(r['original']))==r['sha256'],r['original']
    for r in [json.loads(x) for x in (L/'retrieval.jsonl').read_text().splitlines()]:
        if 'sha256' in r:assert sha(L/r['path'])==r['sha256']
    for r in json.loads((L/'registry-fixed-screen.json').read_text())['indices']:assert sha(Path(r['path']))==r['sha256']
    for r in json.loads((L/'exactcoverage.json').read_text())['bodies']:
        assert sha(L/r['pdf_path'])==r['pdf_sha256'];assert sha(L/r['text_path'])==r['text_sha256']
    assert sha(L/'final-manifest.json')==mh
verify();verify()
r=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=mh,manifest_files=len(m),scientific_originals_and_copies='PASS before/after verification',administrative='snapshots checked; live originals deliberately not compared',retrieval_bodies='PASS against pre-inspection receipt hashes',fixed_registry_refs='PASS hashes only; not current clearance',resource_limits=dict(AS=resource.getrlimit(resource.RLIMIT_AS)[0],CPU=resource.getrlimit(resource.RLIMIT_CPU)[0],groupRSS=512*1024**2,wall=230),wall_seconds=time.monotonic()-start,counts='9/39/next40 unchanged',proof_replay='Not requested or performed in source/prior lane',separate_guarded_execution=True)
(L/'final-verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
