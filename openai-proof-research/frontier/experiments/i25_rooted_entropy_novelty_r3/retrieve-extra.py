import pathlib,json,urllib.request,hashlib,datetime,concurrent.futures,subprocess
root=pathlib.Path(__file__).resolve().parents[3];dest=root/'frontier/sources/i25_rooted_entropy_novelty_r3/literature'
tasks=[('brick-original','1982','pdf','https://link.springer.com/content/pdf/10.1007/BF02579233.pdf'),('cuckler-kahn','author-preprint','pdf','https://citeseerx.ist.psu.edu/document?doi=58aedbe17802b2dcb598f97c4517d823e52a3f40&repid=rep1&type=pdf'),('cuckler-dirac','author-preprint','pdf','https://sites.math.rutgers.edu/~jkahn/Dirac.pdf'),('klee-original','2013','html','https://dmtcs.episciences.org/633'),('klee-original','2013','pdf','https://dmtcs.episciences.org/633/pdf')]
def run(t):
 key,version,kind,url=t;p=dest/(key+'-'+kind+('.pdf' if kind=='pdf' else '.html'));r=dict(key=key,version=version,kind=kind,url=url,retrieved=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=35) as f:b=f.read();r['final_url']=f.url;r['headers']=dict(f.headers)
  p.write_bytes(b);r.update(path=str(p.relative_to(root)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),status='ok')
  if kind=='pdf' and b.startswith(b'%PDF'):
   q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);r['text_path']=str(q.relative_to(root));r['text_sha256']=hashlib.sha256(q.read_bytes()).hexdigest()
 except Exception as ex:r['error']=str(ex);r['status']='error'
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:out=list(pool.map(run,tasks))
(dest/'extra-manifest.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps([{k:r[k] for k in ['key','kind','status','error'] if k in r} for r in out],indent=2))
