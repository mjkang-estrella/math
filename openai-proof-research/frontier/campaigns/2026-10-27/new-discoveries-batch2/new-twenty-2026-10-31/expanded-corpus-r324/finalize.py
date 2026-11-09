R=json.loads((P/'results.json').read_text());V=json.loads((P/'provenance.json').read_text());reserved=json.loads((P/'reservation.json').read_text())['ids']
assert len(R)==20 and set(R)=={str(i) for i in reserved}
for k,v in V.items():
 b=(P/'literal'/f'{k}.raw.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==v['raw_sha256'];assert json.loads(b)==v['parsed']
 assert hashlib.sha256(v['parsed']['statement'].encode()).hexdigest()==v['statement_sha256']
 c=json.dumps(v['parsed'],ensure_ascii=False,sort_keys=True,separators=(',',':')).encode();assert hashlib.sha256(c).hexdigest()==v['parsed_canonical_utf8_sha256']
assert hashlib.sha256((P/'reservation.json').read_bytes()).hexdigest()==(P/'reservation.sha256').read_text().split()[0]
assert not (P/'CANDIDATE.md').exists()
jobs=[json.loads(l) for l in (P/'resources.jsonl').read_text().splitlines()]
report=dict(exact_results=20,raw_parsed_statement_hash_checks=True,reservation_before_after_match=True,accepted_credit=0,pi_handoff=False,launched_sessions_all_completed=True,logged_jobs_before_final=len(jobs),max_logged_self_RSS_KiB=max(j['self_peak_RSS_KiB'] for j in jobs),max_logged_cpu_seconds=max(j['cpu'] for j in jobs),max_logged_wall_seconds=max(j['wall'] for j in jobs),aggregate_sampled_RSS='unavailable')
(P/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
atexit.unregister(savejob);savejob()
manifest={}
for f in sorted(P.rglob('*')):
 if f.is_file() and f.name not in ['manifest.json','manifest.sha256']:
  b=f.read_bytes();manifest[str(f.relative_to(P))]=dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
(P/'manifest.json').write_text(json.dumps(dict(scope='only this lane; manifest excludes itself and manifest.sha256 to avoid recursion',files=manifest),indent=2)+'\n')
(P/'manifest.sha256').write_text(hashlib.sha256((P/'manifest.json').read_bytes()).hexdigest()+'  manifest.json\n')
print(json.dumps(report));print('manifest files',len(manifest))
