exec(compile((__import__('pathlib').Path(__file__).parent/'research.py').read_text(),'research.py','exec'))
import urllib.request,urllib.error,subprocess
if sys.argv[1]=='fetch':
 for url in sys.argv[2:]:
  key=sha(url.encode())[:16]; utc=datetime.datetime.now(datetime.timezone.utc).isoformat(); rec=dict(url=url,utc=utc,method='GET',read_depth='acquired only')
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source reading'}),timeout=18) as f:
    b=f.read(20000000); rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b)); put('sources/'+key+'.raw',b)
    if b.startswith(b'%PDF'):
     q=subprocess.run(['pdftotext','-layout',str(P/'sources'/ (key+'.raw')),str(P/'sources'/(key+'.txt'))],capture_output=True,timeout=20); rec['pdftotext_exit']=q.returncode
    else: put('sources/'+key+'.txt',b.decode(errors='replace'))
  except Exception as e: rec.update(error=str(e))
  js('http/'+key+'.json',rec); print(key,json.dumps(rec))
if sys.argv[1]=='cleanup':
 m=json.loads((P/'history-matches.json').read_bytes()); reduced=[]
 for x in m:
  text=json.dumps(x['record']); excerpts=[]
  for h in x['hits']:
   n=text.find(h); excerpts.append(text[max(0,n-180):n+1100])
  reduced.append(dict(path=x['path'],hits=x['hits'],scoped_excerpts=excerpts))
 js('history-matches.json',reduced)
 for x in reduced: print(json.dumps(x))
 # immutable source references only, not manuscripts yet
 root=P.parents[5]
 for name in ['sources/upstream.json','sources/CONTENTS.md']:
  p=root/name
  if p.exists(): print(name,p.read_text()[:6000])
