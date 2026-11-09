from pathlib import Path
import urllib.request,urllib.error,json,re,hashlib
O=Path(__file__).parent;(O/'sources').mkdir(exist_ok=True);logs=[]
for id in [12330,12490,12493,12861,12594,12723]:
 url=f'https://ems.press/journals/owr/articles/{id}'
 try:
  with urllib.request.urlopen(url,timeout=20) as r: b=r.read(4000000); status=r.status;final=r.url
  (O/f'sources/{id}.html').write_bytes(b)
  s=b.decode();links=re.findall(r'(?:href|content)="([^"]+(?:pdf|\.pdf)[^"]*)"',s)
  logs.append({'url':url,'final_url':final,'status':status,'path':f'sources/{id}.html','sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'pdf_links':list(dict.fromkeys(links))})
 except Exception as e:
  logs.append({'url':url,'failure':str(e)});break
(O/'source-provenance.json').write_text(json.dumps(logs,indent=2)+'\n');print(json.dumps(logs,indent=2))
