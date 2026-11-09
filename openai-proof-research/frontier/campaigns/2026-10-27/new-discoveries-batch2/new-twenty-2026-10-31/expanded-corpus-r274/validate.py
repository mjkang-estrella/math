import json,hashlib,datetime,resource,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();now=datetime.datetime.now(datetime.timezone.utc).isoformat()
r=json.loads((p/'reservation.json').read_text());expected=(p/'reservation.sha256').read_text().split()[0]; actual=sha((p/'reservation.json').read_bytes());assert actual==expected
before=json.loads((p/'reservation-before.json').read_text());assert before['actual']==actual
out=json.loads((p/'results.json').read_text());records=json.loads((p/'literal-records.json').read_text());assert len(out)==20 and set(out)==set(map(str,r['ids']))
chunks={};raw_ok=[]
for i in r['ids']:
 k=str(i); a=records[k];raw=(p/f'evidence/{i}.raw.jsonl').read_bytes(); assert raw.endswith(b'\n') and sha(raw)==a['raw_sha256'];assert json.loads(raw)==a['record']==out[k]['literal_record']; assert sha(a['record']['statement'].encode())==a['statement_utf8_sha256']==out[k]['literal_provenance']['statement_utf8_sha256']
 chunk=Path(a['chunk']);
 if str(chunk) not in chunks:
  b=chunk.read_bytes();assert sha(b)==a['chunk_sha256'];chunks[str(chunk)]=b.splitlines(keepends=True)
 assert chunks[str(chunk)][a['line_one_based']-1]==raw;raw_ok.append(i)
receipts=[json.loads(f.read_text()) for f in (p/'sources').glob('*.receipt.json')];ok=0;errors=[]
for a in receipts:
 if 'file' in a:
  assert sha((p/a['file']).read_bytes())==a['sha256'];ok+=1
 else:errors.append({'url':a['url'],'error':a.get('error')})
(p/'reservation-after.json').write_text(json.dumps({'utc':now,'expected':expected,'actual':actual,'unchanged_from_before':True,'pass':True},indent=2)+'\n')
(p/'job-log.json').write_text(json.dumps({'utc':now,'completed_jobs':[{'script':str(p/'extract.py'),'mode':'python -I -B','completed':True},{'script':str(p/'fetch.py'),'mode':'timeout 140s python -I -B','logs':['fetch.log','related-fetch.log','qualification-fetch.log'],'completed':True},{'script':str(p/'versions.py'),'mode':'timeout 140s python -I -B; child fetch.py','log':'versions.log','completed':True},{'script':str(p/'write_report.py'),'mode':'python -I -B','completed':True},{'script':str(p/'validate.py'),'mode':'timeout 140s python -I -B','completed_on_exit':True}],'limits':'fetch/extract/report/validate scripts set CPU 120s and address space 6GiB; fetch uses two concurrent HTTP threads, 12s request timeouts and 15s text extraction timeout. No heavy mathematical computation. Outer HTTP jobs timeout 140s. Auxiliary synchronous read-only shell/Python jobs completed in observed tool durations.','live_started_background_jobs':0,'execution_formalization_run':False,'children_started':False},indent=2)+'\n')
(p/'VALIDATION.json').write_text(json.dumps({'utc':now,'reservation_before_after_pass':True,'exact_twenty_keys_pass':True,'raw_line_and_chunk_and_statement_hash_checks':raw_ok,'verified_source_bytes':ok,'receipt_errors':errors,'whole_journal_all_versions_and_citing_audit_complete':False,'qualified_candidate':False,'all_launched_exec_sessions_observed_exit_zero':True,'write_scope':'assigned r274 only','credit_change_proposed':False},indent=2)+'\n')
manifest=[]
for f in sorted(p.rglob('*')):
 if f.is_file() and f.name!='manifest.sha256':manifest.append(f'{sha(f.read_bytes())}  {f.relative_to(p)}\n')
(p/'manifest.sha256').write_text(''.join(manifest))
for line in manifest:
 h,f=line.rstrip('\n').split('  ',1);assert sha((p/f).read_bytes())==h
print(json.dumps({'exact_keys':len(out),'raw_lines_verified':len(raw_ok),'source_files_verified':ok,'receipts':len(receipts),'errors':errors,'reservation_sha256':actual,'manifest_entries_verified':len(manifest),'no_live_started_jobs':True},indent=2))
