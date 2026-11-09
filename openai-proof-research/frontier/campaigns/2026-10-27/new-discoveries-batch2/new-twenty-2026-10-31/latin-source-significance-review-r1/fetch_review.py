import urllib.request,urllib.error,hashlib,json,datetime,pathlib,resource
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(45,45))
r=pathlib.Path(__file__).parent
urls={
'arxiv-abs':'https://arxiv.org/abs/2008.11448',
'arxiv-v1.pdf':'https://arxiv.org/pdf/2008.11448v1',
'arxiv-latest.pdf':'https://arxiv.org/pdf/2008.11448',
'published-warwick.pdf':'https://wrap.warwick.ac.uk/id/eprint/170329/1/WRAP-Haystack-hunting-hints-and-locker-room-communication-Kontogeogiou-2022.pdf',
'icalp.pdf':'https://drops.dagstuhl.de/storage/00lipics/lipics-vol198-icalp2021/LIPIcs.ICALP.2021.58/LIPIcs.ICALP.2021.58.pdf',
'openai-head.json':'https://api.github.com/repos/OpenAI/math/commits/HEAD',
'omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'}
rec=[]
for name,url in urls.items():
 d={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalReview/1.0'}),timeout=22) as f:
   data=f.read();d.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(r/name).write_bytes(data)
 except Exception as e:d.update(error=str(e),status=getattr(e,'code',None))
 rec.append(d);print(json.dumps(d),flush=True);(r/'http-receipts.json').write_text(json.dumps(rec,indent=2))
