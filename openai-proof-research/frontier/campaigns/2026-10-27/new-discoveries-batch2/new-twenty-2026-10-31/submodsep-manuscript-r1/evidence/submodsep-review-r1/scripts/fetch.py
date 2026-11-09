from pathlib import Path
import urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys,time
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/submodsep-review-r1')
blocked={'epubs.siam.org','www.sciencedirect.com','api.crossref.org','api.semanticscholar.org','export.arxiv.org'}
class Safe(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in blocked:raise RuntimeError('Blocked redirect '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Safe())
def get(name,url):
 d=L/'downloads'/name;d.mkdir();rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  assert urllib.parse.urlparse(url).hostname not in blocked
  with op.open(urllib.request.Request(url,headers={'User-Agent':'Independent mathematical literature review'}),timeout=18) as f:
   b=f.read(15000000);rec.update(status=f.status,final_url=f.url,headers=dict(f.headers));(d/'body').write_bytes(b);rec.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except urllib.error.HTTPError as e:
  rec.update(status=e.code,error=str(e));
  if e.code in [403,429]:blocked.add(urllib.parse.urlparse(url).hostname)
 except Exception as e:rec['error']=str(e)
 (d/'receipt.json').write_text(json.dumps(rec,indent=2));print(name,rec.get('status'),rec.get('error',''),flush=True)
 return d/'body' if (d/'body').exists() else None
if sys.argv[1]=='sources':
 for name,url in [('arxiv-abs','https://arxiv.org/abs/1902.04740'),('eccc-page','https://eccc.weizmann.ac.il/report/2019/013/'),('eccc-pdf','https://eccc.weizmann.ac.il/report/2019/013/download/'),('author','https://jbrakensiek.github.io/'),('openalex','https://api.openalex.org/works?search='+urllib.parse.quote('CSPs with global modular constraints')+'&per-page=10')]:get(name,url)
if sys.argv[1]=='registry':
 p=get('pool-head','https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD')
 if p:
  sha=json.loads(p.read_text())['sha'];get('pool-projects',f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/projects.yml');get('pool-candidates',f'https://api.github.com/repos/Vilin97/lean-pool/contents/candidates?ref={sha}')
 for i,q in enumerate(['"submodular separation"','"1902.04740"','"Brakensiek" "submodular"']):
  if 'api.github.com' in blocked:break
  time.sleep(7);get(f'github-query-{i}','https://api.github.com/search/repositories?q='+urllib.parse.quote(q)+'&per_page=100')
if sys.argv[1]=='citing':
 data=json.loads((L/'downloads/openalex/body').read_text())
 for a in data['results']:
  print(a['id'],a['title'],a['cited_by_count'],a.get('doi'),flush=True)
  if 'modular constraints' in a['title'].lower():
   get('cites-'+a['id'].split('/')[-1],'https://api.openalex.org/works?filter=cites:'+a['id'].split('/')[-1]+'&per-page=200')
if sys.argv[1]=='papers':
 for name,url in [('structure','https://arxiv.org/pdf/2103.13162'),('nsz','https://arxiv.org/pdf/1707.06212'),('advances','https://arxiv.org/pdf/2302.07029'),('tu','https://arxiv.org/abs/2109.03148')]:get(name,url)
if sys.argv[1]=='pool-content':
 sha=json.loads((L/'downloads/pool-head/body').read_text())['sha']
 get('pool-tree','https://api.github.com/repos/Vilin97/lean-pool/git/trees/'+sha+'?recursive=1')
 for i,p in enumerate(json.loads((L/'downloads/pool-candidates/body').read_text())):
  if p.get('download_url'):get('pool-file-'+str(i),p['download_url'])
if sys.argv[1]=='later':
 for name,url in [('gopi-publications','https://gopisivakanth.github.io/publications/'),('tu-abs','https://arxiv.org/abs/2109.03148'),('cnf-abs','https://arxiv.org/search/?query=CNF+Satisfiability+in+a+Subspace&searchtype=all'),('matroid-abs','https://arxiv.org/search/?query=On+the+Congruency-Constrained+Matroid+Base&searchtype=all')]:get(name,url)
if sys.argv[1]=='finish':
 sha=json.loads((L/'downloads/pool-head/body').read_text())['sha']
 tree=json.loads((L/'downloads/pool-tree/body').read_text())
 print('Pool tree truncated',tree['truncated'])
 for p in tree['tree']:
  if p['path'].endswith('projects.yml'):get('pool-projects-correct','https://raw.githubusercontent.com/Vilin97/lean-pool/'+sha+'/'+p['path']);print('Projects path',p['path'])
 for name,url in [('tu-pdf','https://arxiv.org/pdf/2109.03148v3'),('cnf-pdf','https://arxiv.org/pdf/2108.05914'),('matroid-pdf','https://arxiv.org/pdf/2311.11737')]:get(name,url)
