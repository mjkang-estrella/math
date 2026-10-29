from pathlib import Path
import json,hashlib,datetime
O=Path(__file__).parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((O/'input-freeze.json').read_text()); after=[]
for r in records:
 p=Path(r['path']); q=O/r['copy']; a=h(p); b=h(q)
 after.append(dict(path=r['path'],original_after=a,copy_after=b,expected=r['sha256_before'],match=a==b==r['sha256_before']))
assert all(r['match'] for r in after)
(O/'input-after.json').write_text(json.dumps(after,indent=2))
S=O/'inputs/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-source-discovery-r57/sources'
checks=[]
for name,n,want in [('omega-D5.json',23236,'a279d944837dc2ba420fb86751e9e8449fd6b1c9505adf752e6903f91a58b0b4'),('omega-Problems.json',1551,'5342bf84bed75964dd837e4f610b9bc06d131569e73a0e665822ece2e34aa1ca')]:
 p=S/name; d=json.loads(p.read_text()); assert len(d['tree'])==n and d['truncated']==False and h(p)==want
 checks.append(dict(file=str(p.relative_to(O)),entries=n,truncated=d['truncated'],sha256=h(p),tree_sha=d['sha']))
(O/'scope-check.json').write_text(json.dumps({'cached_named_scopes':checks,'current_head_verified':False,'reason':'fresh GitHub API403 rate limit; no retry; no complete current delta claim'},indent=2))
# Bind downloaded bytes and local extractions before/copy/after into own working evidence snapshot.
new=[]
for p in sorted((O/'evidence').iterdir()):
 if not p.is_file():continue
 before=h(p); q=O/'evidence-frozen'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes())
 new.append(dict(path=str(p.relative_to(O)),copy=str(q.relative_to(O)),sha256_before=before,sha256_copy=h(q),sha256_after=h(p),match=before==h(q)==h(p)))
(O/'evidence-freeze.json').write_text(json.dumps(new,indent=2))
queries=['Bessel function ratio unimodality different orders scales Sturm comparison Karp Vishnyakova Zhang','Sturm Liouville Wronskian Lagrange identity comparison theorem positive solutions ratio one crossing','Bessel ratio unimodality 2026','Bessel Lagrange ratio monotonicity orders','Bessel unimodality Karp proof','Bessel ratio unimodal Wronskian','I unimodality Vishnyakova Zhang Bessel conjecture proof','Relative Oscillation Theory for Sturm Extended 2009']
(O/'search-scope.json').write_text(json.dumps({'utc_date':'2026-10-29','tool':'web search, no browser tools','queries':queries,'use':'lead discovery only; conclusions rely on downloaded/frozen primary bodies','limitations':['not exhaustive','search-result absence not novelty evidence','web radon DistSL open failed; canonical author www PDF fetched normally']},indent=2))
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and p.name!='provenance.json':files.append(dict(path=str(p.relative_to(O)),bytes=p.stat().st_size,sha256=h(p)))
prov=dict(role='independent solo ordinary-proof and eligibility reviewer',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),lane=str(O.resolve()),decisions={'overall':'HOLD','math':'INVEST: ordinary proof sound','source':'INVEST: full published target','novelty':'HOLD: current head blocked; no exact subsumption located in bounded search','substantive':'INVEST provisionally; serious routine-adaptation objection remains'},input_files=len(records),all_input_before_copy_after_and_final_match=all(r['match'] for r in records+after),resource_limits={'AS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'process_group_RSS_MiB':512,'BLAS_threads':1,'monitor_ms':40,'sampling_caveat':True,'Lean_run':False},failures=['GitHub current Omega dev head HTTP403 rate limit; not retried','Nagy URL HTTP200 but 212-byte non-PDF; not relied on','web radon DistSL tool error; normal author www host fetch succeeded'],http_log='http.jsonl',checks=['ownchecks.json','owncheck.log','scope-check.json','input-freeze.json','input-after.json','evidence-freeze.json'],files=files)
(O/'provenance.json').write_text(json.dumps(prov,indent=2))
print(json.dumps({'frozen_inputs':len(records),'unchanged':all(r['match'] for r in after),'cached_scope_validation':'PASS','own_series_certificates':json.loads((O/'ownchecks.json').read_text())['status'],'evidence_files':len(files)}))
