exec(compile(open('investigate.py').read().split("mode=sys.argv[1]")[0],'caps','exec'))
P=json.loads((L/'provenance.json').read_text());R=json.loads((L/'reservation.json').read_text());O=json.loads((L/'results.json').read_text());assert len(O)==20 and set(map(int,O))==set(R['ids']);assert sha((L/'reservation.json').read_bytes())=='f6fb492244c6645afe8b39029511ca8cc3b08d11898a5d9f7e626802eb1c041c'
chunks={};checks=[]
for k,v in P.items():
 p=pathlib.Path(v['chunk']); assert 'pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-' in str(p)
 if p not in chunks:
  b=p.read_bytes();chunks[p]=(sha(b),b.splitlines(keepends=True))
 ch,lines=chunks[p];raw=(L/'literal'/ (k+'.jsonl')).read_bytes();rec=json.loads(raw)
 assert ch==v['chunk_sha256'] and raw==lines[v['line_1based']-1] and sha(raw)==v['raw_sha256'] and raw.endswith(b'\n')
 assert rec==v['record']==json.loads((L/'literal'/(k+'.json')).read_text()) and sha(rec['statement'].encode())==v['statement_sha256']
 assert O[k]['credit']==0;checks.append(int(k))
receipt('verify-bindings',{'true_exit':0,'ids_verified':checks,'unique_corpus_chunks':len(chunks),'no_jobs_spawned':True})
excluded={'artifact-manifest.json','manifest-verification.json'}
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in excluded:
  assert p.resolve().is_relative_to(L) and not p.is_symlink();b=p.read_bytes();rows.append({'path':str(p.relative_to(L)),'bytes':len(b),'sha256':sha(b)})
js('artifact-manifest.json',{'scope':'all lane files except manifest and its final verification receipt, avoiding self-reference','files':rows})
for v in rows:
 b=(L/v['path']).read_bytes();assert len(b)==v['bytes'] and sha(b)==v['sha256']
u=resource.getrusage(resource.RUSAGE_SELF)
js('manifest-verification.json',{'true_exit':0,'verified_files':len(rows),'verified_literal_bindings':len(checks),'reservation_sha256':sha((L/'reservation.json').read_bytes()),'manifest_sha256':sha((L/'artifact-manifest.json').read_bytes()),'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit':120,'as_limit':6*1024**3,'wall_limit':140,'wall_s':time.monotonic()-start,'self_cpu_s':u.ru_utime+u.ru_stime,'self_peak_rss_kib':u.ru_maxrss,'telemetry':'self high-water not concurrent process-group peak','live_children_created':0})
print(json.dumps({'verified_files':len(rows),'literal_bindings':len(checks),'reservation':'unchanged','credit':0,'count':'52/60'}))
