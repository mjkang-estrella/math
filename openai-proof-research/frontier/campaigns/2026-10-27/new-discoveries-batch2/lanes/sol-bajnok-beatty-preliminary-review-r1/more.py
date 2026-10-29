import pathlib,json,urllib.request,datetime,hashlib,subprocess
D=pathlib.Path(__file__).resolve().parent; rows=[]
head=json.loads((D/'research/omega-head.json').read_text())['sha']
urls={'haanpaa.pdf':'https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.pdf','fiber-capacity.md':f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/Blueprint/D5/S1/Deficit/Beatty/FiberCapacityPair.md','bajnok-current.md':f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/Blueprint/D5/S3/FiniteGroups/BajnokBersonJustPerfectRestrictedBasis.md','baseline-to-r89.json':'https://api.github.com/repos/the-omega-institute/trureturing/compare/1b999d9fda71df7537b62327147496d64a6f66ef...e9c949019b00eb22ab88e81d6ac6b1047925d95d'}
for name,url in urls.items():
 row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();row['status']=r.status
  (D/'research'/name).write_bytes(b);row.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:row['error']=str(e)
 rows.append(row)
(D/'research/more-access.json').write_text(json.dumps(rows,indent=2))
if (D/'research/haanpaa.pdf').exists():subprocess.run(['pdftotext','-layout',str(D/'research/haanpaa.pdf'),str(D/'research/haanpaa.txt')],check=True)
for page in [7,8,10,11]:
 subprocess.run(['pdftoppm','-f',str(page),'-l',str(page),'-scale-to','1500','-png','-singlefile',str(D/'copy/sources/bajnok-vor.pdf'),str(D/f'research/vor-p{page-2}')],check=True)
