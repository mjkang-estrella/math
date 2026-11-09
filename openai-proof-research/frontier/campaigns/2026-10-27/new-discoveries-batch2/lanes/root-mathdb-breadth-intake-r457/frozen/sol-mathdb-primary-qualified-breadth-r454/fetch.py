import pathlib,json,hashlib,datetime,urllib.request,urllib.error,re,subprocess
L=pathlib.Path(__file__).resolve().parent;(L/'sources').mkdir(exist_ok=True)
R=json.loads((L/'assigned-records.json').read_text());urls=list(dict.fromkeys(x['record']['source_url'] for x in R));a=[]
def get(url,name):
 row=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),version='publisher response at retrieval UTC')
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research verification'}),timeout=18) as r:
   b=r.read(12000000);row.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),path='sources/'+name);(L/row['path']).write_bytes(b)
 except Exception as e:row.update(status=getattr(e,'code',None),error=str(e))
 a.append(row);(L/'source-provenance.json').write_text(json.dumps(a,indent=2)+'\n');print(url,row.get('status'),row.get('error',''),flush=True)
 return row
for url in urls:
 name=url.rsplit('/',1)[1];r=get(url,name+'.html')
 if r.get('status') in [403,429] or 'error' in r:break
 text=(L/r['path']).read_text(errors='replace')
 if re.search(r'captcha|cf-chl-|Just a moment',text,re.I):r['challenge']=True;break
 pdfs=re.findall(r'(?:href|content)=[\"\x27]([^\"\x27]+\.pdf(?:\?[^\"\x27]*)?)',text)
 print('pdf links',pdfs[:4],flush=True)
 if pdfs:
  purl=urllib.parse.urljoin(url,pdfs[0]);s=get(purl,name+'.pdf')
  if s.get('status') in [403,429]:break
  if 'path' in s:subprocess.run(['pdftotext','-layout',str(L/s['path']),str(L/'sources'/(name+'.txt'))],check=True)
