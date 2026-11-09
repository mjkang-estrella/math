import pathlib,json,hashlib,datetime,resource,subprocess
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((p/'reservation.json').read_bytes());v=json.loads((p/'provenance.json').read_text());result=json.loads((p/'results.json').read_text());expected=(p/'reservation.sha256').read_text().split()[0]
assert sha((p/'reservation.json').read_bytes())==expected
assert list(result)==[str(i) for i in r['ids']] and len(result)==20
chunkhash={}
for k,x in v.items():
 raw=(p/'raw'/f'{k}.jsonl').read_bytes();assert raw.endswith(b'\n') and sha(raw)==x['raw_sha256']
 assert json.loads(raw)==x['record']
 stmt=x['record']['statement'];assert sha(stmt.encode())==x['statement_sha256']
 f=pathlib.Path(x['chunk'])
 if str(f) not in chunkhash:chunkhash[str(f)]=sha(f.read_bytes())
 assert chunkhash[str(f)]==x['chunk_sha256']
 assert f.read_bytes().splitlines(keepends=True)[x['line_1based']-1]==raw
 assert result[k]['literal_statement']==stmt and result[k]['discovery_credit']==0 and not result[k]['pi_handoff_qualified']
receipts=[json.loads(s) for s in (p/'source-receipts.jsonl').read_text().splitlines()]
for x in receipts:
 if 'path' in x:assert sha(pathlib.Path(x['path']).read_bytes())==x['sha256']
ps=subprocess.run(['ps','-eo','pid,ppid,args'],capture_output=True,text=True,check=True).stdout
process_lines=[l for l in ps.splitlines() if '/expanded-corpus-r276/' in l and any('/'+a in l for a in ['fetch.py','fetch-versions.py','fetch-additional.py','fetch-followup.py','extract.py','passages.py','audit.py','write_results.py']) and 'bash -' not in l]
assert not process_lines,process_lines
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_20_keys':True,'all_raw_and_chunk_and_statement_hashes':True,'all_download_receipt_hashes':True,'reservation_match':True,'reservation_sha256':expected,'no_research_fetch_processes':True,'exclusions':sum(x['disposition'].startswith('excluded') for x in result.values()),'no_credit_or_pi_handoff':True,'limits':'No formal theorem checking or independent mathematical acceptance. Process check concerns named scripts in this lane, not unrelated workers.'}
(p/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
(p/'reservation-check-after.json').write_text(json.dumps({'utc':report['utc'],'expected':expected,'actual':expected,'match':True,'exact_keys':True},indent=2)+'\n')
manifest={str(f.relative_to(p)):sha(f.read_bytes()) for f in sorted(p.rglob('*')) if f.is_file() and f.name not in ['manifest.json','manifest.sha256']}
(p/'manifest.json').write_text(json.dumps({'utc':report['utc'],'algorithm':'sha256','excludes':['manifest.json','manifest.sha256'],'files':manifest},indent=2)+'\n');(p/'manifest.sha256').write_text(sha((p/'manifest.json').read_bytes())+'  manifest.json\n')
print(json.dumps(report)); print('Manifest files',len(manifest))
