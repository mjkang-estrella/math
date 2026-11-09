import pathlib,os,resource,subprocess,json,hashlib,zipfile,time,datetime
O=pathlib.Path(__file__).resolve().parent
T=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
F=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(200,200));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
with zipfile.ZipFile(O/'proof-packet.zip','w',zipfile.ZIP_DEFLATED) as z:
 for n in ['Candidate.lean','Audit.lean','replay.py']:z.write(O/n,n)
fresh=O/'fresh-extracted';fresh.mkdir(exist_ok=False)
with zipfile.ZipFile(O/'proof-packet.zip') as z:z.extractall(fresh)
paths=[fresh]+[F/'.lake/packages'/p/'.lake/build/lib/lean' for p in ['mathlib','batteries','Qq','aesop','proofwidgets','LeanSearchClient','importGraph','plausible','Cli']]
env={'PATH':os.defpath,'LEAN_PATH':':'.join(map(str,paths)),'LEAN_NUM_THREADS':'2'}
logs=[]
for args,label in [(['--version'],'version'),(['-o','Candidate.olean','Candidate.lean'],'strict-build'),(['Audit.lean'],'all-declaration-audit')]:
 start=time.time();r=subprocess.run([str(T),'-j2','-M4096','-DwarningAsError=true',*args],cwd=fresh,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=100);(fresh/(label+'.log')).write_bytes(r.stdout);logs.append({'label':label,'exit_code':r.returncode,'seconds':time.time()-start,'log_sha256':sha(fresh/(label+'.log'))})
 if r.returncode:raise RuntimeError(logs)
manifest=json.load(open(F/'lake-manifest.json'));rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lean_binary':str(T),'lean_binary_sha256':sha(T),'mathlib_pin':[p for p in manifest['packages'] if p['name']=='mathlib'],'lake_manifest_sha256':sha(F/'lake-manifest.json'),'packet_sha256':sha(O/'proof-packet.zip'),'sources':{n:sha(fresh/n) for n in ['Candidate.lean','Audit.lean','replay.py']},'logs':logs,'sanitized_environment':list(env),'resource_limits':{'affinity_cpus':sorted(os.sched_getaffinity(0)),'max_virtual_GiB':32,'lean_memory_MiB':4096,'cpu_seconds':200,'wall_seconds_per_process':100,'threads':2},'trust_limit':'External prebuilt package oleans trusted; no full upstream rebuild/source-to-olean attestation.'};(O/'replay-receipt.json').write_text(json.dumps(rec,indent=2));print(json.dumps(rec,indent=2))
