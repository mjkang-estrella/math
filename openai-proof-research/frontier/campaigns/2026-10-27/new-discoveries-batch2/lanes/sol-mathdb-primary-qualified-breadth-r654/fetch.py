from pathlib import Path
import urllib.request,hashlib,json,datetime
O=Path(__file__).resolve().parent
url='https://ems.press/journals/owr/articles/5152'
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=35) as r:
  data=r.read(); final=r.url
 (O/'ems5152.html').write_bytes(data)
 d={'url':url,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':'ems5152.html','sha256':hashlib.sha256(data).hexdigest(),'size':len(data)}
 (O/'source-provenance.json').write_text(json.dumps([d],indent=2)+'\n')
 # Bound bytes before inspecting link content.
 import re
 print('\n'.join(re.findall(r'[^"<>\s]*\.pdf[^"<>\s]*',data.decode())))
except Exception as e:
 (O/'source-provenance.json').write_text(json.dumps([{'url':url,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}],indent=2)+'\n');print(type(e).__name__,str(e))
