exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('r=[]')[0])
jobs={'juhnke-poullot-v3.pdf':'https://arxiv.org/pdf/2504.20739v3','omega-crown.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/549177fd878744e25dce688cbf94dc2955e8958f/Problems/crown-order-polytope-log-concavity.md','poullot-abs.html':'https://arxiv.org/abs/2411.14102','juhnke-poullot-abs.html':'https://arxiv.org/abs/2504.20739'}
r=json.loads((L/'http.json').read_text())
for name,url in jobs.items():
 x={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(12000000);x.update(status=f.status,final_url=f.url)
  p=L/'sources'/name;p.write_bytes(b);x.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:x['error']=str(e)
 r.append(x)
(L/'http.json').write_text(json.dumps(r,indent=2));print(json.dumps(r[-len(jobs):],indent=2))
d=json.loads((L/'sources/omega-delta.json').read_text());print('delta commits',d['total_commits'],'returned',len(d.get('commits',[])),'files',len(d.get('files',[])))
hits=[f for f in d.get('files',[]) if __import__('re').search('poullot|hypersimp|coherent.monotone|grosdos|rooted.product|crown|log.concav',f.get('filename','')+' '+f.get('patch',''),__import__('re').I)]
(L/'delta-hits.json').write_text(json.dumps(hits,indent=2))
