import pathlib,json,urllib.request,hashlib,datetime,re,subprocess
D=pathlib.Path(__file__).resolve().parents[1];receipts=[]
def fetch(url,name):
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check'}),timeout=8) as f:b=f.read();status=f.status
  (D/'sources'/name).write_bytes(b);rec=dict(url=url,file=name,status=status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),utc=datetime.datetime.now(datetime.timezone.utc).isoformat());receipts.append(rec)
  (D/'sources/more-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');return b
 except Exception as e:
  receipts.append(dict(url=url,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));(D/'sources/more-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');return None
for i,o in json.loads((D/'extracted.json').read_text()).items():fetch(o['source_url'],f'{i}-abs.html')
urls=[('https://raw.githubusercontent.com/mysticflounder/schur-degree-block-sums/v1.0.1/paper/schur-degree-block-sums.md','schur-prior.md'),('https://www.numdam.org/item/10.4171/aihpd/67.pdf','ice-journal.pdf'),('https://idus.us.es/server/api/core/bitstreams/1de399e2-12bc-4b46-8342-5923b1ba28e2/content','schur-journal.pdf'),('https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i1p51/pdf/','tournament-neighbour.pdf')]
for url,name in urls:
 b=fetch(url,name)
 if b and name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(D/'sources'/name),str(D/'sources'/name.replace('.pdf','.txt'))],timeout=5)
head=json.loads((D/'sources/the-omega-institute-trureturing-head.json').read_text())['sha'];base='https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'
b=fetch(base+head,'omega-root-tree.json')
if b:
 for x in json.loads(b)['tree']:
  if x['path'] in ['D5','Problems']:
   fetch(base+x['sha']+'?recursive=1','omega-'+x['path']+'-tree.json')
print(json.dumps(receipts,indent=2))
