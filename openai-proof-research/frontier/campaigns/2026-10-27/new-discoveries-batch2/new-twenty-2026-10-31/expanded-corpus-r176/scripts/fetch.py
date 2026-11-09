import urllib.request,urllib.error,urllib.parse,pathlib,json,hashlib,datetime,time,sys
D=pathlib.Path(__file__).resolve().parents[1]; receipts=[];denied=set()
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
opener=urllib.request.build_opener(Redirect)
def get(url,name):
 host=urllib.parse.urlparse(url).hostname
 if host in denied:return None
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with opener.open(urllib.request.Request(url,headers={'User-Agent':'mathematical-research-source-review'}),timeout=20) as r:
   b=r.read(15000000);rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/'sources'/name).write_bytes(b)
 except Exception as e:
  rec['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   rec['status']=e.code
   if e.code in (403,429):denied.add(host)
  b=None
 receipts.append(rec);(D/'outputs'/('fetch-'+sys.argv[1]+'.json')).write_text(json.dumps(receipts,indent=2)+'\n');print(name,rec.get('status'),rec.get('error',''),flush=True);return b
mode=sys.argv[1]
if mode=='sources':
 for row in json.loads((D/'reservation.json').read_text())['rows']:
  a=row['source_url'].rsplit('/',1)[1]
  if (D/'sources'/f'{a}-abs.html').exists():continue
  get('https://arxiv.org/abs/'+a,a+'-abs.html');get('https://arxiv.org/html/'+a,a+'-body.html')
if mode=='registries':
 reg={}
 for repo in ['Vilin97/lean-pool','the-omega-institute/trureturing','openai/math']:
  key=repo.split('/')[-1];b=get(f'https://api.github.com/repos/{repo}/commits/HEAD',key+'-head.json')
  if not b:continue
  sha=json.loads(b)['sha'];reg[repo]={'head':sha}
  tree=get(f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1',key+'-tree.json')
  if repo=='Vilin97/lean-pool' and tree:
   paths=[x['path'] for x in json.loads(tree)['tree'] if x['type']=='blob' and (x['path']=='projects.yml' or x['path'].startswith('candidates/'))]
   for n,p in enumerate(paths):get(f'https://raw.githubusercontent.com/{repo}/{sha}/{p}',f'lean-pool-file-{n}.txt')
 (D/'outputs/registry-screen.json').write_text(json.dumps({'registries':reg,'receipts':receipts,'github_search':'pending','scope':'path and metadata screen, not Lean replay'},indent=2)+'\n')
if mode=='github':
 queries=['"Mycielskian" lean','"sum-free" "inverse" lean','"zero-sum" "Cichacz" lean','"Saxl" lean','"radial Moore" lean','"rainbow arborescence" lean','"Thue Morse" "3/2" lean','"Doolittle" lean']
 out=[]
 for j,q in enumerate(queries):
  if j:time.sleep(8)
  b=get('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),f'github-search-{j}.json');out.append({'query':q,'result':json.loads(b) if b else None})
  if 'api.github.com' in denied:break
 p=D/'outputs/registry-screen.json';r=json.loads(p.read_text());r['github_search']=out;r['github_receipts']=receipts;p.write_text(json.dumps(r,indent=2)+'\n')
