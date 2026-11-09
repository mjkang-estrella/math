import runpy
D=runpy.run_path(__file__.replace('jfetch.py','research.py'));globals().update({k:v for k,v in D.items() if not k.startswith('__')})
import urllib.request,base64
http=[]
for aid in sys.argv[1:]:
 url={'nenashev-final':'https://www.combinatorics.org/ojs/index.php/eljc/article/download/v6i1p32/pdf','fkm-final':'https://www.combinatorics.org/ojs/index.php/eljc/article/download/v23i1p24/pdf'}[aid];t=now()
 try:
  with urllib.request.urlopen(url,timeout=24) as r:b=r.read();status=r.status;final=r.url
  rec={'url':url,'utc':t,'status':status,'final_url':final,'bytes':len(b),'sha256':sha(b),'depth':'acquisition only until text passages separately read'};http.append(rec)
  write('sources/'+aid+'.pdf.b64',base64.b64encode(b).decode())
  p=subprocess.Popen(['pdftotext','-layout','-','-'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
  # communicate joined through capped process, PDF tool does not spawn descendants.
  import threading
  result={}
  def communicate():result['v']=p.communicate(b,timeout=30)
  th=threading.Thread(target=communicate);th.start();samples=[]
  while th.is_alive():
   try:
    s=pathlib.Path(f'/proc/{p.pid}/status').read_text();rss=int(s.split('VmRSS:')[1].split()[0]) if 'VmRSS:'in s else 0;samples.append(rss)
    if rss>6*1024**2:os.killpg(p.pid,9)
   except FileNotFoundError:pass
   time.sleep(.01)
  th.join();out,err=result['v'];rc=p.wait();receipts.append({'kind':'converter','utc':t,'pid':p.pid,'true_exit':rc,'reaped':True,'rss_kib_samples':samples,'stderr':err.decode()});assert rc==0
  write('sources/'+aid+'.txt',out.decode());print(aid,len(b),len(out),rc)
 except Exception as e:http.append({'url':url,'utc':t,'error':str(e),'no_retry':True});print(aid,'ERROR',str(e))
write('http-'+ '-'.join(sys.argv[1:])+'.json',http);write('resources-'+ '-'.join(sys.argv[1:])+'.json',receipts)
print('TRUE_EXIT',0,'PID',os.getpid(),'RUSAGE',list(resource.getrusage(resource.RUSAGE_SELF)))
