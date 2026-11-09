import pathlib,urllib.request,urllib.error,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent
out=[]
for name,aid in [('commutative','1803.03457'),('fishburn','2208.01484'),('young','1410.0106')]:
 url='https://arxiv.org/html/'+aid
 e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'requested_version':'arXiv latest HTML; exact version must be read from body'}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();e.update(final_url=r.url,status=r.status)
  (P/(name+'.html')).write_bytes(b);e.update(path=name+'.html',sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as ex:e['error']=str(ex)
 out.append(e)
(P/'downloads.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
