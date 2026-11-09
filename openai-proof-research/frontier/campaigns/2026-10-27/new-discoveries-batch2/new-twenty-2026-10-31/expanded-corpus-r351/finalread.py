import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib
exec(compile((pathlib.Path(__file__).parent/'worker.py').read_text().split('code=0')[0],'worker.py','exec'))
inv=[]
for fn,pat,last in [('2310.18163.html.txt','12 A boundedness',True),('2306.01724.html.txt','Torso-extensions vs',True),('bergeron.pdf.txt','Corollary 9.29.',True),('2302.04783.html.txt','Conjecture',True),('2509.19905.html.txt','repeat',False)]:
 t=read(P/'sources'/fn).decode();ms=list(re.finditer(re.escape(pat),t,re.I));m=ms[-1] if last and ms else ms[0] if ms else None
 if m:
  a=max(0,m.start()-100);b=min(len(t),m.start()+2200);print(fn,a,b,t[a:b]);inv.append({'file':fn,'range':[a,b]})
for n in ['upstream.json','CONTENTS.md']:
 f=P.parents[5]/'sources'/n
 if f.is_file(): b=read(f);print('READ',f,len(b));print(b.decode()[:800])
t=read(P/'sources/leanpool-candidates.html').decode();paths=sorted(set(re.findall(r'"path":"(candidates/[^"\n]+)"',t)));print('ROUTING PATHS',paths[:25]);save('registry-routing.json',{'leanpool_head':'49bdad2b2b82b4b41d75a8e251ac10b2aa08fb45','formalization_corpus_head':'337c09aed2de34876cf280ffe5c0c6b92e432530','candidate_paths':paths,'projects_yml':'404 at attempted current path; not cleared','import_index':'root LeanPool.lean has no list; routing only','gate':'HOLD, no proof absence inferred'})
u=resource.getrusage(resource.RUSAGE_SELF);save('receipts/process-'+token+'.json',{'exit':0,'limits':[2,120,140,6*1024**3],'affinity':sorted(os.sched_getaffinity(0)),'self_peak_RSS_KiB':u.ru_maxrss,'cpu':u.ru_utime+u.ru_stime,'reads':reads,'display':inv})
