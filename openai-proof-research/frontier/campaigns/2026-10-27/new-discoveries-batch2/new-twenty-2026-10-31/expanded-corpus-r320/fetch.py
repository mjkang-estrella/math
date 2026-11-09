import os,resource,pathlib,urllib.request,time,json,hashlib,sys,html,re
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent; start=time.monotonic(); (p/'sources').mkdir(exist_ok=True)
for key,url in json.loads(sys.argv[1]):
 rec={'key':key,'url':url,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-reader/1.0'}),timeout=18) as r:
   b=r.read(6000001);assert len(b)<=6000000;rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/'sources'/key).write_bytes(b)
   if b'<html' in b.lower() or b'<!doctype' in b.lower():
    s=b.decode('utf-8',errors='replace');s=re.sub(r'<(script|style)\b[^>]*>.*?</\1>','',s,flags=re.S);s=re.sub('<[^>]+>',' ',s);s=html.unescape(s);s=re.sub(r'[ \t]+',' ',s);(p/'sources'/(key+'.txt')).write_text(s)
 except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
 with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec),flush=True)
print('RESOURCE',json.dumps({'wall_s':time.monotonic()-start,'cpu_s':resource.getrusage(resource.RUSAGE_SELF).ru_utime+resource.getrusage(resource.RUSAGE_SELF).ru_stime,'self_highwater_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'group_sampled_RSS':'unavailable','affinity':list(os.sched_getaffinity(0))}))
