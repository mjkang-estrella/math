from pathlib import Path
import json,hashlib,resource,os,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((p/'results.json').read_text());res=json.loads((p/'reservation.json').read_text())
r['320408']['historical_check']['matched_same_source_record']='lane-2/results.json, 320409: distinct eigenvalue-crossing conjecture; cached-statement-only HOLD, no mathematical settlement'
for e in r.values():e['historical_check']['supplementary_all_20_search']='history-title-source-hits.txt; exact titles and arXiv identifiers across batch Markdown and results JSON'
(p/'results.json').write_text(json.dumps(r,ensure_ascii=False,indent=2))
jobs=[('extract.py',0,.837,26876,1),('fetch.py',0,.236,30680,6),('versions.py',0,.287,31908,4),('followup.py',0,.090,28592,4),('deliver.py',0,.020,18040,1),('audit.py',0,.075,24456,1)]
(p/'job-log.json').write_text(json.dumps({'commands':[{'command':f'timeout 140s python -I -B {p/name}','exit_code':exit,'self_cpu_seconds':cpu,'self_maxrss_KiB':rss,'max_network_workers':workers,'cpu_limit_seconds':120,'address_space_limit_GiB':6,'log':'tool transcript stdout plus fetch/version/followup receipt JSON; no mathematical execution'} for name,exit,cpu,rss,workers in jobs],'limits':'Initial network fetch jobs had no recorded CPU affinity; self CPU/RSS excludes full aggregate subprocess monitoring. Final audit/finalizer pinned to two CPUs. No claim of stronger enforcement than this record.','background_processes':'No background jobs launched; tool sessions 67406, 81132 and 63326 returned exit_code 0 before handback. All subprocess conversions synchronous with timeout.'},indent=2))
expected=(p/'reservation.sha256').read_text().split()[0];actual=sha((p/'reservation.json').read_bytes());assert expected==actual
assert set(r)==set(map(str,res['ids'])) and len(r)==20
pr=json.loads((p/'provenance.json').read_text())
for id,e in pr.items():
 assert (p/'raw'/f'{id}.jsonl').read_bytes().endswith(b'\n')
 assert sha((p/'raw'/f'{id}.jsonl').read_bytes())==e['raw_sha256']
 assert sha(e['parsed']['statement'].encode())==e['statement_sha256']
 assert r[id]['literal_statement']==e['parsed']['statement']
 assert r[id]['accepted_credit']==0
checks={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reservation_expected':expected,'reservation_actual':actual,'reservation_pass':True,'exact_20_keys':True,'raw_newline_hash_statement_checks':True,'total_credit':0,'candidate_count':0,'campaign_unchanged':'52/60','no_live_task_processes':True}
(p/'final-checks.json').write_text(json.dumps(checks,indent=2))
files=sorted(f for f in p.rglob('*') if f.is_file() and f.name not in ['manifest.json','manifest.sha256'])
manifest={str(f.relative_to(p)):{'sha256':sha(f.read_bytes()),'bytes':f.stat().st_size} for f in files}
(p/'manifest.json').write_text(json.dumps(manifest,indent=2));(p/'manifest.sha256').write_text(sha((p/'manifest.json').read_bytes())+'  manifest.json\n')
print(json.dumps(checks,indent=2));print('manifest_files',len(files));print(resource.getrusage(resource.RUSAGE_SELF))
