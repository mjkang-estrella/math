import pathlib,hashlib,json,urllib.request,urllib.parse,datetime,subprocess,sys
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def log(name,r):
 with (L/name).open('a') as f:f.write(json.dumps(r)+'\n')
def fetch(key,url):
 assert not any(x in url.lower() for x in ['google','github','sciencedirect'])
 p=L/'primary'/key;p.parent.mkdir(exist_ok=True)
 r=dict(key=key,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Academic source verification'}),timeout=25) as q:
   data=q.read(16000000);r.update(status=q.status,final_url=q.url)
  p.write_bytes(data);r.update(sha256=sha(p),bytes=len(data),frozen_before_read=True)
 except Exception as e:r['error']=str(e)
 log('access.jsonl',r);print(json.dumps(r))
def extract(p):
 p=pathlib.Path(p);h=sha(p);d=L/'texts'/(p.stem+'.txt');d.parent.mkdir(exist_ok=True)
 subprocess.run(['pdftotext','-layout',str(p),str(d)],check=True)
 assert sha(p)==h
 log('sourcebindings.jsonl',dict(source=str(p),source_sha256=h,text=str(d),text_sha256=sha(d)))
 print(str(d))
if __name__=='__main__' and sys.argv[1]=='fetch':fetch(*sys.argv[2:])
elif __name__=='__main__' and sys.argv[1]=='extract':extract(sys.argv[2])
elif __name__=='__main__' and sys.argv[1]=='initial':
 # Repair the administrative basename collision; both snapshots retained distinctly.
 R=L.parents[5];p=R/'AGENTS.md';d=L/'administrative'/'ancestor-AGENTS.md';d.write_bytes(p.read_bytes())
 records=json.loads((L/'freeze-bindings.json').read_text());records[0]['copy']=str(d);(L/'freeze-bindings.json').write_text(json.dumps(records,indent=2))
 for name in ['ledger.json','prior-campaign-context.json']:
  obj=json.loads((L/'administrative'/name).read_text());print(name,json.dumps(obj)[:22000])
 extract(L/'frozen'/'primary'/'1412.7488v4.pdf')
 fetch('shuffle-current.atom','https://export.arxiv.org/api/query?id_list=1412.7488')
 fetch('shuffle-successors.atom','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('all:"random-to-random" AND (all:poset OR all:"linear extensions")')+'&max_results=20&sortBy=lastUpdatedDate&sortOrder=descending')
 fetch('shuffle-bing.html','https://www.bing.com/search?q='+urllib.parse.quote('"Ayyer" "Schilling" "Thiéry" "conjecture" random random proof'))
