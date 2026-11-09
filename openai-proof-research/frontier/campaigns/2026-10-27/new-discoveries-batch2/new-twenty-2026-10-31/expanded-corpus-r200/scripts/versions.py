import pathlib,json,re,sys,subprocess
D=pathlib.Path(__file__).resolve().parents[1]; urls=[]
for p in (D/'sources').glob('*/receipt.json'):
 r=json.loads(p.read_text())
 if '/abs/' not in r['url'] or r.get('status')!=200:continue
  # all historic bodies; current unversioned already retained
 s=(p.parent/'body').read_text();ns=[int(x) for x in re.findall(r'\[v(\d+)\]',s)];n=max(ns or [1])
 for v in range(1,n):urls.append(r['url'].replace('/abs/','/pdf/')+f'v{v}')
subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*urls],check=True)
