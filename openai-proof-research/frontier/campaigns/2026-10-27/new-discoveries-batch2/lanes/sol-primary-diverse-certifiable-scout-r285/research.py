import pathlib,hashlib,json,urllib.request,subprocess,sys,time,re
L=pathlib.Path(__file__).resolve().parent
def sha(d): return hashlib.sha256(d).hexdigest()
def record(row):
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
def freeze(p,url=None,original=None):
 d=p.read_bytes(); h=sha(d)
 record(dict(path=str(p.relative_to(L)),sha256=h,bytes=len(d),url=url,original=original,time=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())))
 p.chmod(0o444)
 assert sha(p.read_bytes())==h
 return d
def fetch(key,url):
 p=L/'primary'/key
 if p.exists():raise RuntimeError('refuse overwrite')
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=25) as r:
   d=r.read(16000000); status=r.status
  p.write_bytes(d);freeze(p,url)
  if d.startswith(b'%PDF'):
   t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);freeze(t,'derived:'+key)
  print(key,status,len(d))
 except Exception as e:
  with (L/'access-failures.jsonl').open('a') as f:f.write(json.dumps(dict(url=url,key=key,error=str(e),time=time.time()))+'\n')
  print(key,str(e))
if __name__=='__main__':
 if sys.argv[1]=='search':
  p=L/'primary/search.html';d=freeze(p,'https://arxiv.org/search/?query=conjectures&searchtype=title&abstracts=show&order=-announced_date_first&size=50').decode()
  import html
  for r in d.split('<li class="arxiv-result">')[1:]:
   ident=re.search(r'href="https://arxiv.org/abs/([^"]+)',r)
   title=re.search(r'<p class="title[^>]*>(.*?)</p>',r,re.S)
   authors=re.search(r'<p class="authors[^>]*>(.*?)</p>',r,re.S)
   clean=lambda x:html.unescape(re.sub('<[^>]+>',' ',x)).strip()
   print(ident.group(1) if ident else '?',clean(title.group(1)) if title else '?',clean(authors.group(1)) if authors else '?')
 elif sys.argv[1]=='fetch':fetch(sys.argv[2],sys.argv[3])
