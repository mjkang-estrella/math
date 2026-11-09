import pathlib,re,json,hashlib,csv
r=pathlib.Path.cwd(); p=r/'fresh';mods=(p/'modules.txt').read_text().splitlines();rows=[]
for m in mods:
 row={'module':m}
 assert (p/f'logs/replay/{m}.ok').exists(),m
 for kind in ('lean','checker'):
  s=(p/f'logs/replay/{m}.{kind}.log').read_text()
  assert 'resource_exit=0' in s and 'RSS watchdog killed' not in s,m
  row[kind+'_peak_rss_KiB']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s)[1])
  row[kind+'_wall']=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.*)',s)[1]
 rows.append(row)
with (r/'replay-table.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
endpoint=(p/'logs/replay/Round2Audit.lean.log').read_text()
line=next(l for l in endpoint.splitlines() if "'Round2.literal_negation' depends on axioms" in l)
assert '[propext, Classical.choice, Quot.sound]' in line,line
for name in ['Audit','AuditPartial','Round2Audit','Round2AuditPartial']:
 assert 'metadata clean' in (p/f'logs/replay/{name}.lean.log').read_text(),name
z=r/'source.zip';h=hashlib.sha256(z.read_bytes()).hexdigest()
result=dict(mathdb_id=352253,round=3,status='COMPLETE_REPLAY_NOT_ACCEPTANCE',accepted=False,credit=0,source_zip_sha256=h,module_count=len(mods),fresh_lean_passed=len(rows),fresh_explicit_module_leanchecker_passed=len(rows),endpoint='Round2.literal_negation',endpoint_axioms=['propext','Classical.choice','Quot.sound'],lean_peak_rss_KiB=max(x['lean_peak_rss_KiB'] for x in rows),checker_peak_rss_KiB=max(x['checker_peak_rss_KiB'] for x in rows),limits=dict(lean_M_MiB=3500,RSS_KiB=6291456,cpu_seconds=120,wall_seconds=140,cpus=2,MALLOC_ARENA_MAX=2),metadata_audits=['Audit','AuditPartial','Round2Audit','Round2AuditPartial'],source_scan='passed',data_and_original_statements_unchanged=True,per_module_resources='replay-table.csv',remaining='Root independent review and acceptance; no implementation obligation remains if all assertions pass.')
(r/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
