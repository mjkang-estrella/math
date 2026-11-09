import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,runpy,urllib.request,datetime,subprocess,threading,time,json
sys.argv.append('bodies');g=runpy.run_path(str(pathlib.Path(__file__).with_name('research.py')));L=g['L'];js=g['js'];write=g['write'];sha=g['sha']
# Prior HTTP requests succeeded; repeat solely to recover bytes lost to unavailable parser. No access denial retry.
items=[('spectral','https://arxiv.org/pdf/2007.08956'),('matching','https://arxiv.org/pdf/2004.14049'),('metric','https://arxiv.org/pdf/2010.10326'),('staged','https://arxiv.org/pdf/2010.15515'),('spectral-journal','https://archive.intlpress.com/site/pub/files/_fulltext/journals/joc/2023/0014/0004/JOC-2023-0014-0004-a002.pdf')]
out=[]
for n,u in items:
 r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'name':n}
 try:
  with urllib.request.urlopen(u,timeout=15) as f:b=f.read(8000000);r.update(status=f.status,finalURL=f.url,bytes=len(b),sha256=sha(b))
  p=subprocess.Popen(['/usr/bin/pdftotext','-layout','-','-'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  samples=[];stop=threading.Event()
  def guard():
   while not stop.wait(.01):
    try:
     s=pathlib.Path('/proc/'+str(p.pid)+'/status').read_text();rss=next(int(x.split()[1]) for x in s.splitlines() if x.startswith('VmRSS:'));samples.append(rss)
     if rss>1000000:p.kill()
    except (OSError,StopIteration):pass
  t=threading.Thread(target=guard);t.start()
  try:o,e=p.communicate(b,timeout=25)
  except subprocess.TimeoutExpired:p.kill();o,e=p.communicate();r['timeout']=True
  finally:stop.set();t.join()
  r.update(true_exit=p.returncode,sampled_RSS_KiB=samples,stderr=e.decode(errors='replace'),child_reaped=True,read_depth='extracted only; see read inventory');write('sources/'+n+'.txt',o)
 except Exception as e:r.update(error=repr(e),status=getattr(e,'code',None))
 out.append(r);print(json.dumps(r))
js('http-bodies.json',out)
