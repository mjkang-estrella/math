import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,runpy,urllib.request,datetime,hashlib,json,time
sys.argv.append('acquire');g=runpy.run_path(str(pathlib.Path(__file__).with_name('research.py')));L=g['L'];js=g['js'];write=g['write'];sha=g['sha']
import concurrent.futures
urls=[('spectral-abs','https://arxiv.org/abs/2007.08956'),('spectral','https://arxiv.org/pdf/2007.08956'),('matching-abs','https://arxiv.org/abs/2004.14049'),('matching','https://arxiv.org/pdf/2004.14049'),('metric-abs','https://arxiv.org/abs/2010.10326'),('metric','https://arxiv.org/pdf/2010.10326'),('staged-abs','https://arxiv.org/abs/2010.15515'),('staged','https://arxiv.org/pdf/2010.15515')]
def fetch(t):
 n,u=t;r={'name':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=18) as f:b=f.read(8000000);r.update(status=f.status,finalURL=f.url,bytes=len(b),sha256=sha(b))
  if b.startswith(b'%PDF'):
   import fitz
   d=fitz.open(stream=b,filetype='pdf');s='\n'.join(p.get_text() for p in d);r.update(pages=len(d),stored='sources/'+n+'.txt',read_depth='acquired/extracted only until explicit passage read');write(r['stored'],s)
  else:write('sources/'+n+'.html',b);r.update(stored='sources/'+n+'.html',read_depth='acquired only')
 except Exception as e:r.update(error=repr(e),status=getattr(e,'code',None),read_depth='failed; no retry')
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:out=list(e.map(fetch,urls))
js('http-acquire.json',out)
for x in out:print(json.dumps(x))
