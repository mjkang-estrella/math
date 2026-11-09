import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,subprocess,sys,time
lane=pathlib.Path(__file__).resolve().parent
names=['REVIEW.md','review.json','keyed355433-review.json','objections.json','source-inventory.json','read-inventory.json','reads.jsonl','history-receipt.json','access.json','web-evidence.json','execution-receipt.json','bootstrap-receipt.json','frozen-before.json','frozen-after.json','TASK.txt','target-record.json','ROOT-PREPARATION.json','launch.json','historical-results-allowlist.json','frozen-inputs.json','bootstrap.py','verify_frozen.py','write_lane.py','read_sources.py','inspect.py','keyed.py','fetch.py','finish.py','manifest_check.py','sources/openai.html','sources/leanpool.html','sources/arxiv.html']
def put(n,j):subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),n],input=json.dumps(j,indent=2)+'\n',text=True,check=True,stdout=subprocess.DEVNULL)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest={n:digest(lane/n) for n in names};put('manifest.json',manifest)
loaded=json.loads((lane/'manifest.json').read_text());bad=[n for n,h in loaded.items() if digest(lane/n)!=h]
for n in ['frozen-before.json','frozen-after.json']:
 r=json.loads((lane/n).read_text());assert r['count']==306 and r['mismatches']==[]
put('manifest-verification.json',{'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'manifest_sha256':digest(lane/'manifest.json'),'files_verified':len(loaded),'mismatches':bad,'frozen_before':306,'frozen_after':306,'credit':0,'accepted':52,'target':60,'caps_before_reads':True,'allowed_cpus':sorted(os.sched_getaffinity(0)),'self_high_water_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'exit_intended':0 if not bad else 1,'scope':'Lane output files only; no outside/protected path traversal'})
print(json.dumps({'files_verified':len(loaded),'mismatches':bad,'frozen_before_after':'306/306 unchanged'}));sys.exit(bool(bad))
