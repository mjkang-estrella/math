import pathlib,json,urllib.request,hashlib,datetime,concurrent.futures,subprocess
root=pathlib.Path(__file__).resolve().parents[3]; dest=root/'frontier/sources/i25_rooted_entropy_novelty_r3/literature';dest.mkdir(parents=True,exist_ok=True)
papers={'gurvits':'1106.2844v11','cube-ideal':'2505.14497v2','singh-vishnoi':'1304.8108v1','dong-jain-girth':'2609.02017v1','dong-jain-permanent':'2609.11049v1','bootstrap':'1306.1267v3','tight-cuts':'2605.25695v1','anari-entropy':'1806.05567v3','regular-expanding':'2103.08683v1','cubic-counts':'1012.2878v2','uncrossing':'1704.01929v2','alternative-entropy':'2607.15549v1'}
tasks=[]
for key,aid in papers.items():
 for kind in ['abs','pdf']:
  tasks.append((key,aid,kind,'https://arxiv.org/'+kind+'/'+aid))
 tasks.append((key,aid,'current','https://arxiv.org/abs/'+aid.split('v')[0]))
tasks += [('edmonds','1965','pdf','https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn1-2p125_A1b.pdf'),('anari-focs','2018','pdf','https://ieee-focs.org/FOCS-2018-Papers/pdfs/59f035.pdf')]
def run(t):
 key,version,kind,url=t;p=dest/(key+'-'+kind+('.pdf' if kind=='pdf' else '.html'));r=dict(key=key,version=version,kind=kind,url=url,retrieved=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0 research review'}),timeout=40) as f:b=f.read();r['final_url']=f.url;r['headers']=dict(f.headers)
  p.write_bytes(b);r.update(path=str(p.relative_to(root)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),status='ok')
  if kind=='pdf' and b.startswith(b'%PDF'):
   q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);r['text_path']=str(q.relative_to(root));r['text_sha256']=hashlib.sha256(q.read_bytes()).hexdigest()
 except Exception as ex:r['error']=str(ex);r['status']='error'
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool: out=list(pool.map(run,tasks))
(dest/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ['key','kind','status','error'] if k in r} for r in out],indent=2))
