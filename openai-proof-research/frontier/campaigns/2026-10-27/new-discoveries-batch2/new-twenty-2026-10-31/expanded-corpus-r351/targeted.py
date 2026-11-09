import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib
exec(compile((pathlib.Path(__file__).parent/'worker.py').read_text().split('code=0')[0],'worker.py','exec'))
specs=[('2310.18163.html.txt','boundedness'),('2311.10956.html.txt','Conjecture'),('2602.08738.html.txt','Conjecture'),('2302.04783.html.txt','minimal class'),('2606.14974.html.txt','Conjecture'),('2606.24326.html.txt','conjecture'),('2607.08630.html.txt','Conjecture'),('2306.01724.html.txt','torso'),('2509.19905.html.txt','non-deterministic'),('color-companion.html.txt','5-cycle'),('speyer-companion.html.txt','Theorem 4.3'),('treewidth-refutation.html.txt','Theorem 5.2'),('bergeron.pdf.txt','Corollary 9.29'),('2503.01032.html.txt','Theorem 1.1')]
inv=[]
for fn,pat in specs:
 t=read(P/'sources'/fn).decode();ms=list(re.finditer(re.escape(pat),t,re.I));m=ms[-1] if fn.startswith('treewidth') else (ms[0] if ms else None)
 if m:
  a=max(0,m.start()-150);b=min(len(t),m.start()+2300);print('\nFILE',fn,'RANGE',a,b);print(t[a:b]);inv.append({'file':fn,'range':[a,b]})
 else:print('NO MATCH',fn,pat)
save('targeted-read-inventory.json',inv)
u=resource.getrusage(resource.RUSAGE_SELF);save('receipts/process-'+token+'.json',{'exit':0,'limits':[2,120,140,6*1024**3],'affinity':sorted(os.sched_getaffinity(0)),'self_peak_RSS_KiB':u.ru_maxrss,'cpu':u.ru_utime+u.ru_stime,'reads':reads,'display':inv})
