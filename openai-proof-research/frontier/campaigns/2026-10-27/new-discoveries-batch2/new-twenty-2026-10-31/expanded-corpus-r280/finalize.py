import pathlib,json,hashlib,resource,os,time,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));start=time.monotonic()
r=pathlib.Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();data=json.loads((r/'results.json').read_text());res=json.loads((r/'reservation.json').read_text());assert set(data)==set(map(str,res['ids'])) and len(data)==20
chunks={};checks=[]
for k,v in data.items():
 p=v['provenance'];path=pathlib.Path(p['chunk_path'])
 if str(path) not in chunks:
  b=path.read_bytes();chunks[str(path)]=(sha(b),b.splitlines(keepends=True))
 ch,ls=chunks[str(path)];line=ls[p['line_1based']-1]
 assert ch==p['chunk_sha256'];assert sha(line)==p['raw_sha256'];assert line==(r/p['raw_file']).read_bytes();assert json.loads(line)==v['full_parsed_record'];assert sha(v['literal_statement'].encode())==p['statement_utf8_sha256'];checks.append(k)
expected=(r/'reservation.sha256').read_text().split()[0];assert sha((r/'reservation.json').read_bytes())==expected
live=[]
for proc in pathlib.Path('/proc').iterdir():
 if not proc.name.isdigit() or int(proc.name)==os.getpid():continue
 try:
  parts=(proc/'cmdline').read_bytes().split(b'\0'); exe=parts[0].decode(errors='replace')
  if 'python' in exe and any(str(r).encode() in x for x in parts[1:]):live.append({'pid':proc.name,'argv':[x.decode(errors='replace') for x in parts if x]})
 except (FileNotFoundError,PermissionError,ProcessLookupError):pass
assert not live,live
external={}
for p in [r.parents[5]/'AGENTS.md',r.parent/'AGENTS.md',r.parent/'ledger.json',r.parent/'STATUS.md',r.parent.parent/'AGENTS.md',r.parent.parent/'ledger.json',r.parent.parent/'prior-campaign-context.json',r.parents[5]/'sources/upstream.json',r.parents[5]/'sources/CONTENTS.md']:
 if p.exists():external[str(p)]={'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
(r/'external-inputs.json').write_text(json.dumps(external,indent=2)+'\n')
log={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'commands':['python -I -B extract.py','python -I -B history.py','python -I -B fetch.py abs','python -I -B fetch.py pdf','python -I -B extra.py','python -I -B supplement.py','python -I -B assemble.py','python -I -B finalize.py'],'resource_limits_for_named_scripts':{'cpu_seconds_hard':120,'address_space_bytes':6*1024**3,'fetch_threads_max':2,'per_http_timeout_seconds':12,'per_pdf_text_timeout_seconds':15},'wall_limit_note':'Named jobs completed within 140 seconds; interactive command completion receipts remain in tool transcript. No external watchdog was installed and historical CPU/RSS per job was not independently sampled.','errors_preserved':['Initial extra.py invocation failed with undefined __file__; corrected and rerun.','Optional BeautifulSoup import unavailable; used standard-library HTMLParser.','Two journal HTTP 403s; guessed community projects and omega URLs HTTP 404. No bypass.'],'exact_20_raw_records_revalidated':checks,'reservation_sha256':expected,'active_lane_python_processes':live,'background_jobs_launched':False,'final_validation_wall_seconds':time.monotonic()-start,'finalizer_cpu_usage_seconds':resource.getrusage(resource.RUSAGE_SELF).ru_utime+resource.getrusage(resource.RUSAGE_SELF).ru_stime,'finalizer_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(r/'validation.json').write_text(json.dumps(log,indent=2)+'\n')
files=sorted(p for p in r.rglob('*') if p.is_file() and p.name!='manifest.sha256')
(r/'manifest.sha256').write_text(''.join(sha(p.read_bytes())+'  '+str(p.relative_to(r))+'\n' for p in files))
for l in (r/'manifest.sha256').read_text().splitlines():h,name=l.split('  ',1);assert sha((r/name).read_bytes())==h
print(json.dumps({'records':len(checks),'reservation_unchanged':True,'manifest_files':len(files),'manifest_verified':True,'active_lane_python_processes':live}))
