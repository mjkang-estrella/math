import pathlib,json,urllib.request,urllib.error,hashlib,datetime,sys,time
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166')
def fetch(url,name):
 p=D/'sources'/name;p.parent.mkdir(exist_ok=True,parents=True)
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=18) as f:b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));p.write_bytes(b)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 with (D/'outputs/http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(name,r.get('status'),r.get('error',''),flush=True)
 return json.loads(p.read_text()) if p.exists() and name.endswith('.json') else None
if sys.argv[1]=='registry':
 for repo,key in [('Vilin97/lean-pool','lean-pool'),('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
  j=fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',key+'-head.json')
  if j:
   sha=j['sha'];fetch(f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1',key+'-tree.json')
   if key=='lean-pool':fetch(f'https://raw.githubusercontent.com/{repo}/{sha}/projects.yml','projects.yml')
else:
 rows=json.loads((D/'reservation.json').read_text())['rows'];sel=set(map(int,sys.argv[1:]))
 for r in rows:
  if r['mathdb_id'] in sel:
   aid=r['source_url'].rsplit('/',1)[1];fetch('https://arxiv.org/abs/'+aid,str(r['mathdb_id'])+'-abs.html');fetch('https://arxiv.org/pdf/'+aid,str(r['mathdb_id'])+'.pdf')
