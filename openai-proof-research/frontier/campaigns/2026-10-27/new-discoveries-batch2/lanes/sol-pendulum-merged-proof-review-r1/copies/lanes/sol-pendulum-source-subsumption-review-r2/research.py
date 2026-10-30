import sys,pathlib,json,urllib.request,urllib.error,hashlib,datetime,re,html
O=pathlib.Path(__file__).parent
for name,url in json.loads(sys.argv[1]):
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Scholarly evidence review (public sources)'}),timeout=22) as f:
   data=f.read(16000001); assert len(data)<=16000000
   r.update(status=f.status,final_url=f.url,content_type=f.headers.get('Content-Type'),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  (O/'research').mkdir(exist_ok=True); (O/'research'/name).write_bytes(data)
  if 'pdf' not in r['content_type']:
   s=data.decode('utf-8','replace'); s=re.sub(r'<(script|style)\b[^>]*>.*?</\1>','',s,flags=re.S|re.I); s=html.unescape(re.sub('<[^>]+>',' ',s)); s=re.sub(r'\s+',' ',s)
   (O/'research'/(name+'.txt')).write_text(s)
   print(name,s[:18000])
 except Exception as e:r['error']=str(e); print(name,str(e))
 with (O/'retrievals.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
