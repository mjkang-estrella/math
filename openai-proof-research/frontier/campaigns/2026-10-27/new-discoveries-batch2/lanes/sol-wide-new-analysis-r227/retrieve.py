import urllib.request,urllib.error,pathlib,json,hashlib,datetime,sys,subprocess
L=pathlib.Path(__file__).resolve().parent
def fetch(url,name):
 p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research/1.0 (bounded primary-source reading)'}),timeout=35) as r:
   data=r.read(12000000);rec.update(status=r.status,final_url=r.url)
  if b'captcha' in data[:5000].lower() or b'challenge-platform' in data[:5000].lower():raise RuntimeError('challenge: stop route')
  p.write_bytes(data);rec.update(path=str(p),sha256=hashlib.sha256(data).hexdigest(),size=len(data))
  (L/'sourcebytes.jsonl').open('a').write(json.dumps(rec)+'\n')
  assert hashlib.sha256(p.read_bytes()).hexdigest()==rec['sha256']
  if name.endswith('.pdf'):
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  return data
 except Exception as e:
  rec['error']=str(e);(L/'failures.jsonl').open('a').write(json.dumps(rec)+'\n');print(rec);return b''
if __name__=='__main__':
 if sys.argv[1]=='api':
  import urllib.parse
  q='(all:conjecture OR all:"open question") AND (cat:math.CA OR cat:math.PR OR cat:math.MG)'
  d=fetch('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&start=0&max_results=40&sortBy=submittedDate&sortOrder=descending','search.xml')
  print(d.decode()[:65000])
 else:fetch(sys.argv[1],sys.argv[2])
