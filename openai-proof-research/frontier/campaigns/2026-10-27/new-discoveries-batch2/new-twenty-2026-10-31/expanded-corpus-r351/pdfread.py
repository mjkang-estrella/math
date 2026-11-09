import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib
exec(compile((pathlib.Path(__file__).parent/'worker.py').read_text().split('code=0')[0],'worker.py','exec'))
import subprocess
runs=[]
for n in ['roberson','bergeron']:
 f=P/'sources'/(n+'.pdf')
 if f.is_file():
  dest=(P/'sources'/(n+'.pdf.txt')).resolve();assert dest.is_relative_to(P)
  r=subprocess.run(['pdftotext','-layout',str(f),str(dest)],capture_output=True,timeout=40);runs.append({'argv':['pdftotext','-layout',str(f),str(dest)],'true_exit':r.returncode,'stderr':r.stderr.decode()});print(n,r.returncode)
u=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN);save('receipts/process-'+token+'.json',{'exit':0,'limits':[2,120,140,6*1024**3],'affinity':sorted(os.sched_getaffinity(0)),'self_peak_RSS_KiB':u.ru_maxrss,'reaped_child_peak_RSS_KiB':c.ru_maxrss,'self_cpu':u.ru_utime+u.ru_stime,'child_cpu':c.ru_utime+c.ru_stime,'wall':time.monotonic()-started,'jobs':runs,'telemetry':'self and reaped child peaks, not concurrent group peak; all subprocess.run calls joined'})
