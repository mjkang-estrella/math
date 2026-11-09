from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
O=Path(__file__).resolve().parent;p=O/'ems5152.pdf';url='https://content.ems.press/assets/public/full-texts/serials/owr/8/2/5152/online/10.4171-owr-2011-24.pdf'
a=json.loads((O/'source-provenance.json').read_text())
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=35) as r:data=r.read();final=r.url
 p.write_bytes(data);a.append({'url':url,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':p.name,'sha256':hashlib.sha256(data).hexdigest(),'size':len(data)})
 (O/'source-provenance.json').write_text(json.dumps(a,indent=2)+'\n')
 subprocess.run(['pdftotext','-layout',str(p),str(O/'ems5152.txt')],check=True)
 p=O/'ems5152.txt';a.append({'derived_from':'ems5152.pdf','tool':'pdftotext -layout','path':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size})
 (O/'source-provenance.json').write_text(json.dumps(a,indent=2)+'\n')
 s=p.read_text();j=s.find('diam');print(s[max(0,j-3000):j+3500])
except Exception as e:print(type(e).__name__,e)
