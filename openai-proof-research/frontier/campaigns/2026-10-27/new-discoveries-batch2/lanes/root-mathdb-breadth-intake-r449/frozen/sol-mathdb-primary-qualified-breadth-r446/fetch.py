import urllib.request,urllib.error,pathlib,json,hashlib,datetime,re,subprocess
R=pathlib.Path(__file__).resolve().parent;(R/'sources').mkdir(exist_ok=True)
urls={
'owr2018-50.html':'https://ems.press/journals/owr/articles/16633',
'owr2019-13.html':'https://ems.press/journals/owr/articles/16775',
'owr2019-19.html':'https://ems.press/journals/owr/articles/16931',
'owr2019-27.html':'https://ems.press/journals/owr/articles/16939',
'owr2019-39.html':'https://ems.press/journals/owr/articles/17135',
'owr2019-47.html':'https://ems.press/journals/owr/articles/17290',
'heisenberg.pdf':'https://arxiv.org/pdf/1902.05475',
'determinant.pdf':'https://arxiv.org/pdf/1805.11245',
'scaling.pdf':'https://arxiv.org/pdf/2008.11388',
'multiscale.pdf':'https://arxiv.org/pdf/1910.13492'}
log=[];blocked=set()
def get(n,u):
 host=urllib.request.urlparse(u).netloc if False else __import__('urllib.parse',fromlist=['urlparse']).urlparse(u).netloc
 if host in blocked:return
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research source verification'}),timeout=22) as r:
   data=r.read(16000000);dest=r.url
  (R/'sources'/n).write_bytes(data)
  e={'file':'sources/'+n,'url':u,'final_url':dest,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'status':'downloaded','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};log.append(e)
  if n.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(R/'sources'/n),str(R/'sources'/n.replace('.pdf','.txt'))],check=True)
  return data
 except Exception as e:
  log.append({'url':u,'file':n,'status':'HOLD','error':str(e)})
  if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):blocked.add(host)
for n,u in urls.items():get(n,u)
# Publisher-provided PDF links only, no guessed alternate paths.
for n in list(urls):
 if not n.endswith('.html') or not (R/'sources'/n).exists():continue
 s=(R/'sources'/n).read_text(errors='replace');matches=re.findall(r'https://ems\.press/content/[^"<> ]+\.pdf',s)
 if matches:get(n.replace('.html','.pdf'),matches[0].replace('&amp;','&'))
(R/'source-access.json').write_text(json.dumps(log,indent=2)+'\n');print(json.dumps(log,indent=2))
