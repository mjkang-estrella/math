from pathlib import Path
import urllib.request,urllib.error,json,re,subprocess,hashlib
R=Path(__file__).parent;(R/'primary').mkdir(exist_ok=True);log=[]
def get(url,name):
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=25) as f:
   b=f.read(10000000);status=f.status;final=f.url
  p=R/'primary'/name;p.write_bytes(b);log.append({'url':url,'final_url':final,'path':str(p.relative_to(R)),'status':status,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()});return b
 except Exception as e:log.append({'url':url,'failure':str(e),'retry':False});return None
for n in [1464,1596,1782,1783]:
 b=get(f'https://ems.press/journals/owr/articles/{n}',f'{n}.html')
 if b:
  links=re.findall(r'href="([^"]+)"',b.decode())
  urls=[x for x in links if 'serial-article-files' in x]
  if urls:
   url=urls[0];url='https://ems.press'+url if url.startswith('/') else url
   pdf=get(url,f'{n}.pdf')
   if pdf:subprocess.run(['pdftotext','-layout',str(R/'primary'/f'{n}.pdf'),str(R/'primary'/f'{n}.txt')],check=True)
for n in ['1407.4726v2','1906.10213']:
 b=get('https://arxiv.org/pdf/'+n,n+'.pdf')
 if b:subprocess.run(['pdftotext','-layout',str(R/'primary'/(n+'.pdf')),str(R/'primary'/(n+'.txt'))],check=True)
(R/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(json.dumps(log,indent=2))
