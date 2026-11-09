from research import *
import os,resource
m=json.loads((L/'final-manifest.json').read_text());failed=[]
for rel,d in m.items():
 p=L/rel
 if h(p)!=d['sha256'] or p.stat().st_size!=d['bytes']:failed.append(rel)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in {'final-manifest.json','final-verification.json'}}
assert set(m)==actual
source_count=0
for line in (L/'bindings.jsonl').read_text().splitlines():
 d=json.loads(line);assert h(pathlib.Path(d['pdf']))==d['pdf_sha256'];assert h(pathlib.Path(d['text']))==d['text_sha256'];source_count+=1
frozen_count=0
for d in json.loads((L/'provenance.json').read_text()):
 if d['kind']=='scientific frozen':assert h(pathlib.Path(d['original']))==d['sha256']==h(pathlib.Path(d['copy']));frozen_count+=1
refs=json.loads((L/'history-reused.json').read_text())
for d in refs:assert h(pathlib.Path(d['path']))==d['sha256']
assert not failed
receipt=dict(status='PASS',utc=str(datetime.datetime.now(datetime.timezone.utc)),manifest_sha256=h(L/'final-manifest.json'),manifest_entries=len(m),scientific_source_bindings=source_count,original_copy_scientific_pairs=frozen_count,immutable_history_references=len(refs),failed=failed,manifest_excludes=['final-manifest.json','final-verification.json'],AS_soft=resource.getrlimit(resource.RLIMIT_AS)[0],CPU_soft=resource.getrlimit(resource.RLIMIT_CPU)[0],OPENBLAS_NUM_THREADS=os.getenv('OPENBLAS_NUM_THREADS'),OMP_NUM_THREADS=os.getenv('OMP_NUM_THREADS'),scope='Integrity verification only; not independent mathematical or novelty acceptance')
(L/'final-verification.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
