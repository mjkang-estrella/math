import runpy
D=runpy.run_path(__file__.replace('public.py','research.py'));globals().update({k:v for k,v in D.items() if not k.startswith('__')})
import urllib.request,re
h=[]
for name,url in [('nenashev-journal','https://www.combinatorics.org/ojs/index.php/eljc/article/view/v6i1p32'),('fkm-companion','https://www.combinatorics.org/ojs/index.php/eljc/article/view/v23i1p24'),('nenashev-arxiv-metadata','https://arxiv.org/abs/1803.09966'),('pierson-arxiv-metadata','https://arxiv.org/abs/2408.01390'),('dimuro-arxiv-metadata','https://arxiv.org/abs/1805.11641')]:
 t=now()
 try:
  with urllib.request.urlopen(url,timeout=18) as r:b=r.read();status=r.status;final=r.url
  s=b.decode();write('sources/'+name+'.html',s);h.append({'url':url,'utc':t,'status':status,'final_url':final,'bytes':len(b),'sha256':sha(b),'depth':'metadata/links and version history only'})
  print(name)
  for line in s.splitlines():
   if any(w in line.lower() for w in ['citation_pdf_url','submission-history','dateline','v1]','v2]','v3]','doi.org','download/','correction','erratum']):print(line[:1800])
 except Exception as e:h.append({'url':url,'utc':t,'error':str(e),'no_retry':True});print(name,'ERROR',str(e))
write('public-access.json',h);write('public-resources.json',receipts);print('TRUE_EXIT',0,'PID',os.getpid(),'RUSAGE',list(resource.getrusage(resource.RUSAGE_SELF)))
