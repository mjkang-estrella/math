import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib
exec(compile((pathlib.Path(__file__).parent/'worker.py').read_text().split('code=0')[0],'worker.py','exec'))
for n in ['roberson-proof.html','bergeron-current.html','treewidth-journal.html','leanpool-github.html']:
 t=read(P/'sources'/n).decode(); print(n,sorted(set(x for x in re.findall(r'(?:href|src)="([^"]+)"',t) if any(k in x for k in ['.pdf','/pdf/','/files/','candidates','projects.yml','All.lean']))))
u=resource.getrusage(resource.RUSAGE_SELF);save('receipts/process-'+token+'.json',{'exit':0,'limits':[2,120,140,6*1024**3],'affinity':sorted(os.sched_getaffinity(0)),'self_peak_RSS_KiB':u.ru_maxrss,'cpu':u.ru_utime+u.ru_stime,'reads':reads})
