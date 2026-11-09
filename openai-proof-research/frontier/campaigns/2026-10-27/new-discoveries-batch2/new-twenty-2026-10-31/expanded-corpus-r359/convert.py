import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,subprocess,json,time,sys
L=pathlib.Path(__file__).resolve().parent;rows=[]
for name in sys.argv[1:]:
 p=(L/'sources'/name).resolve();assert p.is_relative_to(L) and p.exists();out=p.with_suffix('.txt');t=time.monotonic();r=subprocess.run(['pdftotext','-layout',str(p),str(out)],capture_output=True,timeout=35);rows.append({'input':name,'exit':r.returncode,'stderr':r.stderr.decode(),'wall':time.monotonic()-t});assert r.returncode==0
(L/('conversion-receipt-'+str(time.time_ns())+'.json')).write_text(json.dumps({'rows':rows,'exit':0,'all_children_reaped':True,'self_rusage':list(resource.getrusage(resource.RUSAGE_SELF)),'reaped_children_rusage':list(resource.getrusage(resource.RUSAGE_CHILDREN)),'telemetry':'not concurrent group peak'},indent=2)+'\n')
