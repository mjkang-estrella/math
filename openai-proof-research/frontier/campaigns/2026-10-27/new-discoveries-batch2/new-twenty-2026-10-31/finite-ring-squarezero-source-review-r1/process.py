import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import runpy,sys,json,base64,re,subprocess,threading,time,pathlib
D=runpy.run_path(__file__.replace('process.py','audit.py'));read=D['read'];write=D['write'];L=D['L'];items=D['items']
# Guard adapted from author research.py, inspected in full. No mathematical execution.
def convert(b):
 p=subprocess.Popen(['pdftotext','-layout','-','-'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE);stop=threading.Event();peak=[0];t=time.monotonic()
 def guard():
  while not stop.is_set():
   try:
    s=pathlib.Path('/proc/'+str(p.pid)+'/status').read_text();rss=int(s.split('VmRSS:')[1].split()[0]);peak[0]=max(peak[0],rss)
    if rss>1048576:p.kill()
   except (FileNotFoundError,IndexError,ProcessLookupError):pass
   stop.wait(.01)
 th=threading.Thread(target=guard);th.start()
 try:out,err=p.communicate(b,timeout=60)
 except subprocess.TimeoutExpired:p.kill();out,err=p.communicate()
 finally:stop.set();th.join()
 items.append({'conversion_exit':p.returncode,'reaped':True,'guard_joined':True,'RSS_sample_peak_KiB':peak[0],'RSS_limit_KiB':1048576,'wall_cap_s':60,'wall':time.monotonic()-t,'stderr':err.decode()});assert p.returncode==0;return out.decode()
mode=sys.argv[1]
for name in sys.argv[2:]:
 s=read(L/('fresh/'+name+'.b64'));b=base64.b64decode(s)
 if mode=='convert':
  s=convert(b);write('fresh/'+name+'.txt',s);print(name,len(s));continue
 s=b.decode(errors='replace');print('FILE',name)
 if mode=='registry':
  if 'head' in name:print('\n'.join(s.splitlines()[:8]));continue
  if 'tree' in name:
   for blob in re.findall(r'<script[^>]*type="application/json"[^>]*>(.*?)</script>',s,re.S):
    try:
     j=json.loads(blob)
     def walk(x):
      if isinstance(x,dict):
       if 'path' in x and 'name' in x:print(x['path'])
       for v in x.values():walk(v)
      elif isinstance(x,list):
       for v in x:walk(v)
     walk(j)
    except ValueError:pass
  elif name=='fish-history':
   for line in s.splitlines():
    if re.search('v[12345]|201[78]|journal_ref|Comments|version',line):print(line[:500])
  else:
   blocks=s.split('<td>');hits=[x for x in blocks if re.search(r'finite commutative ring|difference sets|Fish|square.zero|335255|nilpotent',x,re.I)];print('TARGETED BLOCKS',len(hits));print('\n'.join(hits)[:22000])
 elif mode=='text':print(s)
write('receipts/process-'+D['stamp']+'.json',json.dumps(items,indent=2))
