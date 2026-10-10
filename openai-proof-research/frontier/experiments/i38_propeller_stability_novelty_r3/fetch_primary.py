from pathlib import Path
import requests,json,hashlib,datetime,subprocess,concurrent.futures
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i38_propeller_stability_novelty_r3/literature'
urls={
'hjn-author.pdf':'https://web.math.princeton.edu/~naor/homepage%20files/PropR3.pdf',
'kn-author.pdf':'https://web.math.princeton.edu/~naor/homepage%20files/kernel.pdf',
'hei14-author.pdf':'https://www.stevenheilman.org/~heilman/papers/SSC.pdf',
'corthree-author.pdf':'https://www.stevenheilman.org/~heilman/papers/corthree.pdf',
'stable-author.pdf':'https://www.stevenheilman.org/~heilman/papers/stable.pdf',
'bfh-published.pdf':'https://publikationen.bibliothek.kit.edu/1000129550/102192820',
}
ids={'hjn':'1112.2993','corthree':'2306.03312','stable':'1901.03934','dimred':'2011.05583','hyperstable':'2209.11216','robust':'2108.04950','carlen':'1609.00936','bfh':'2001.10706','bfh-sym':'2410.11460','fgs':'2609.38904','klz':'1511.08479','simplex-current-new':'2607.14087'}
versions={'hjn':2,'corthree':3,'stable':1,'dimred':2,'hyperstable':1,'robust':1,'carlen':1,'bfh':1,'bfh-sym':1,'fgs':1,'klz':1,'simplex-current-new':1}
for key,id in ids.items():
 urls[key+'-current.html']='https://arxiv.org/abs/'+id
 urls[key+'-v'+str(versions[key])+'.pdf']='https://arxiv.org/pdf/'+id+'v'+str(versions[key])
def one(kv):
 name,url=kv;entry={'name':name,'request':{'method':'GET','url':url,'headers':{'User-Agent':'I38 mathematical significance review'}},'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(url,headers=entry['request']['headers'],timeout=45);data=r.content;(S/name).write_bytes(data)
  entry.update(status=r.status_code,final_url=r.url,headers=dict(r.headers),bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),valid_pdf=data.startswith(b'%PDF'))
  if entry['valid_pdf']:
   p=subprocess.run(['pdftotext','-layout',str(S/name),str(S/Path(name).with_suffix('.txt'))],capture_output=True,text=True);entry.update(extraction_returncode=p.returncode,extraction_stderr=p.stderr)
 except Exception as e:entry['error']=repr(e)
 return entry
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:out=list(pool.map(one,urls.items()))
(S/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{k:r.get(k) for k in ['name','status','bytes','error']} for r in out],indent=2))
