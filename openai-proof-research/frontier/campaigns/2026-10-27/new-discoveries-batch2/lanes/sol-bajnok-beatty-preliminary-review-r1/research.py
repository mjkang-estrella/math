import pathlib,urllib.request,json,datetime,hashlib,subprocess
D=pathlib.Path(__file__).resolve().parent; (D/'research').mkdir(exist_ok=True); rows=[]
urls={'dougherty-faber.pdf':'https://arxiv.org/pdf/math/9412223','haanpaa.html':'https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa2.html','omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD','beatty-research.html':'https://wkylebeatty.com/research/'}
for name,url in urls.items():
 row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalReview/1.0'}),timeout=25) as r: b=r.read();row.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(D/'research'/name).write_bytes(b)
 except Exception as e:row['error']=str(e)
 rows.append(row)
(D/'research/access.json').write_text(json.dumps(rows,indent=2))
if (D/'research/dougherty-faber.pdf').exists(): subprocess.run(['pdftotext','-layout',str(D/'research/dougherty-faber.pdf'),str(D/'research/dougherty-faber.txt')],check=True)
subprocess.run(['pdftoppm','-f','5','-l','5','-scale-to','1600','-png','-singlefile',str(D/'copy/sources/bajnok-vor.pdf'),str(D/'research/vor-p3')],check=True)
subprocess.run(['pdftoppm','-f','9','-l','9','-scale-to','1600','-png','-singlefile',str(D/'copy/sources/bajnok-vor.pdf'),str(D/'research/vor-p7')],check=True)
