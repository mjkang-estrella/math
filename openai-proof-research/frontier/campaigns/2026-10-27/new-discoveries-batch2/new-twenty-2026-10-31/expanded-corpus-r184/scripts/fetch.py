import pathlib,urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys,time
D=pathlib.Path(__file__).resolve().parents[1]; receipts=[]; denied=set()
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied: raise RuntimeError('denied redirect host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Redirect)
def get(url,name):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlparse(url).hostname in denied: raise RuntimeError('host denied earlier')
  with op.open(urllib.request.Request(url,headers={'User-Agent':'mathematics-research/1.0'}),timeout=18) as f: b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/'sources'/name).write_bytes(b)
 except Exception as e:
  r['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   r['status']=e.code
   if e.code in (403,429): denied.add(urllib.parse.urlparse(url).hostname)
 receipts.append(r);(D/'outputs'/f'receipts-{sys.argv[1]}.json').write_text(json.dumps(receipts,indent=2));return r
if sys.argv[1]=='registry':
 heads={}
 for repo,tag in [('Vilin97/lean-pool','pool'),('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
  r=get(f'https://api.github.com/repos/{repo}/commits/HEAD',tag+'-head.json')
  if r.get('status')==200: heads[tag]=json.loads((D/'sources'/f'{tag}-head.json').read_text())['sha']
 if 'pool' in heads:
  s=heads['pool'];get(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{s}/projects.yml','pool-projects.yml')
  r=get(f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{s}?recursive=1','pool-tree.json')
  if r.get('status')==200:
   for x in json.loads((D/'sources/pool-tree.json').read_text())['tree']:
    if x['type']=='blob' and x['path'].startswith('candidates/'):
     get(f"https://raw.githubusercontent.com/Vilin97/lean-pool/{s}/{x['path']}",'pool-'+x['path'].replace('/','--'))
 (D/'outputs/registry-screen.json').write_text(json.dumps({'heads':heads,'receipts':receipts,'queries':[],'limitation':'Pending keyword/body comparison; path listings alone do not clear proofs.'},indent=2))
elif sys.argv[1]=='papers':
 rows=json.loads((D/'reservation.json').read_text())['rows']
 for row in rows[int(sys.argv[2]):int(sys.argv[3])]:
  a=row['source_url'].split('/')[-1]
  if (D/'sources'/f'{a}.pdf').exists():continue
  get('https://arxiv.org/abs/'+a,a+'.html');get('https://arxiv.org/pdf/'+a,a+'.pdf')
elif sys.argv[1]=='queries':
 queries=['"2011.02685" lean','"2011.12822" lean','"1903.00419" lean','"2011.04410" lean','"2012.13164" lean','"1903.07375" lean','"2011.10791" lean','"2012.03230" lean']
 out=json.loads((D/'outputs/registry-screen.json').read_text())
 for j,q in enumerate(queries):
  r=get('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),f'github-query-{j}.json');r['query']=q;out['queries'].append(r)
  if r.get('status') in (403,429):break
  time.sleep(8)
 out['query_receipts']=receipts;(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
