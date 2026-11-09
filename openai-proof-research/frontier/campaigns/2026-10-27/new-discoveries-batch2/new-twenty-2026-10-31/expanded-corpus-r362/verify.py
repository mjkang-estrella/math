exec(compile((__import__('pathlib').Path(__file__).resolve().parent/'research.py').read_text(),'research.py','exec'))
pv=json.loads((L/'provenance.json').read_text());rs=json.loads((L/'results.json').read_text())
assert len(rs)==20 and set(rs)==set(map(str,r['ids']))
chunkcache={}
for k,v in pv.items():
 p=pathlib.Path(v['chunk'])
 if str(p) not in chunkcache:
  b=p.read_bytes();chunkcache[str(p)]=(sha(b),b.splitlines(keepends=True))
 ch,lines=chunkcache[str(p)];raw=(L/'literal'/(k+'.jsonl')).read_bytes()
 assert ch==v['chunk_sha256'] and raw==lines[v['line_one_based']-1] and raw.endswith(b'\n')
 assert sha(raw)==v['raw_sha256'];obj=json.loads(raw)
 assert obj==v['record']==json.loads((L/'parsed'/(k+'.json')).read_text())
 assert sha(obj['statement'].encode())==v['statement_sha256']
 assert obj['statement']==rs[k]['literal_statement'] and rs[k]['credit']==0
checks=[json.loads((L/n).read_text()) for n in ['reservation-before.json','reservation-after.json']]
assert all(v['sha256']==sha((L/'reservation.json').read_bytes()) for v in checks)
http=[json.loads(p.read_text()) for p in (L/'http').iterdir()]
receipt('pre-manifest-verification',dict(exact_bindings_verified=20,http_receipts=len(http),successful_GETs=sum(x.get('status')==200 for x in http),failed_GETs=sum(x.get('status')!=200 for x in http),all_started_command_sessions_returned=True))
files={}
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['MANIFEST.json','MANIFEST-VERIFIED.json']:
  assert p.resolve().is_relative_to(L);files[str(p.relative_to(L))]=dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes()))
js('MANIFEST.json',dict(files=files,excluded=['MANIFEST.json','MANIFEST-VERIFIED.json'],reservation_sha256=sha((L/'reservation.json').read_bytes())))
manifest=json.loads((L/'MANIFEST.json').read_text())
for n,v in manifest['files'].items():
 b=(L/n).read_bytes();assert len(b)==v['bytes'] and sha(b)==v['sha256']
js('MANIFEST-VERIFIED.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified=True,artifacts=len(files),manifest_sha256=sha((L/'MANIFEST.json').read_bytes()),exact_results=20,raw_corpus_bindings_verified=20,reservation_before_after=True,credit=0,campaign='52/60 unchanged',wall_seconds=time.monotonic()-start,affinity=list(os.sched_getaffinity(0)),self_peak_RSS_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,telemetry='self high-water only, no group/cgroup peak claim'))
print(json.dumps(dict(verified_artifacts=len(files),exact_results=20,GET_receipts=len(http),reservation=sha((L/'reservation.json').read_bytes()),credit=0)))
