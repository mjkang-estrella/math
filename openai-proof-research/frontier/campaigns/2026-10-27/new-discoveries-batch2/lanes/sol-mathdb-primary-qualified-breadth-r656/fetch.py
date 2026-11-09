import urllib.request,pathlib,hashlib,json,datetime
p=pathlib.Path(__file__).resolve().parent
url='https://ems.press/journals/owr/articles/11136'
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=30) as r:data=r.read();final=r.url;status=r.status
 (p/'ems11136.html').write_bytes(data)
 entry={'url':url,'final_url':final,'status':status,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':'ems11136.html','sha256':hashlib.sha256(data).hexdigest(),'size':len(data),'coverage':'bytes bound; content not yet read'}
except Exception as e:entry={'url':url,'error':str(e),'stopped':True}
(p/'source-provenance.json').write_text(json.dumps([entry],indent=2)+'\n');print(entry)
