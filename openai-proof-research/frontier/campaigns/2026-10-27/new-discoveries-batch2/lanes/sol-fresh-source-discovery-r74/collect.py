import pathlib,json,hashlib,urllib.request,datetime,subprocess,re
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent; R=B.parents[3]
def sha(b):return hashlib.sha256(b).hexdigest()
receipt=[]
for p in [B/'AGENTS.md',B/'NEXT.md',B/'ledger.json',B/'prior-campaign-context.json',R/'AGENTS.md']:
 b=p.read_bytes();receipt.append({'path':str(p),'sha256':sha(b),'bytes':len(b)})
 if p.suffix=='.json':
  j=json.loads(b); (L/('context-'+p.name)).write_text(json.dumps(j,indent=2))
for p in sorted(L.parent.glob('*/SUMMARY.md')):
 b=p.read_bytes();s=b.decode(errors='replace');m=re.search(r'discovery-r(\d+)$',p.parent.name)
 if m and 57<=int(m[1])<=72 or re.search('Chernoff|Balabdaoui|Wellner|Palafox|479107|481234|2005.10930|2111.06997',s,re.I):
  receipt.append({'path':str(p),'sha256':sha(b),'bytes':len(b),'text':s})
# Full ledger/context parsed, plus bounded older/all lane summaries lexical screen before selection.
(L/'context-reading.json').write_text(json.dumps(receipt,indent=2))
regs=[]
for p in (L.parent/'sol-fresh-source-discovery-r57'/'sources').glob('*.json'):
 try:j=json.loads(p.read_text())
 except:continue
 hits=[]
 def walk(x):
  if isinstance(x,dict):
   if isinstance(x.get('path'),str) and re.search(r'chernoff|balabdaoui|wellner|lyapunov|palafox|renyi|rényi|airy',x['path'],re.I):hits.append(x)
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(j)
 regs.append({'file':str(p),'sha256':sha(p.read_bytes()),'hits':hits})
(L/'registry-cache-screen.json').write_text(json.dumps(regs,indent=2))
urls={
 'renyi-original.pdf':'https://www.math.cmu.edu/users/ttkocz/mypapers/mathematics/renyi-discr-comp.pdf',
 'lyapunov.pdf':'https://arxiv.org/pdf/2111.06997',
 'chernoff-original.pdf':'https://sites.stat.washington.edu/jaw/JAW-papers/jaw-balabdaoui.bj.14.pdf',
 'chernoff-new.html':'https://arxiv.org/html/2607.18619v1',
 'chernoff-abs.html':'https://arxiv.org/abs/2607.18619',
 'omega-readme.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/main/README.md',
}
records=[]
for name,url in urls.items():
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=22) as f:b=f.read(12000000);r.update(status=f.status,headers=dict(f.headers))
  (L/r['file']).write_bytes(b);r.update(bytes=len(b),sha256=sha(b))
  if b'%PDF'==b[:4]:
   subprocess.run(['pdftotext','-layout',str(L/r['file']),str(L/'sources'/name.replace('.pdf','.txt'))],check=True)
  elif re.search(b'captcha|incapsula|security challenge|verify you are human',b,re.I):r['access_limit']='possible security challenge; stop route, no retry'
 except Exception as e:r['error']=str(e)
 records.append(r);(L/'http.json').write_text(json.dumps(records,indent=2))
print(json.dumps({'reads':len(receipt),'registry_hits':regs,'http':records},indent=2))
