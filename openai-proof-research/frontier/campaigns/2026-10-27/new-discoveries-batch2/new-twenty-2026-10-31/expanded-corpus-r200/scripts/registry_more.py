import pathlib,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
urls=[]
for repo in ['openai/math','the-omega-institute/trureturing']:
 for p in (D/'sources').glob('*/receipt.json'):
  r=json.loads(p.read_text())
  if r['url']==f'https://api.github.com/repos/{repo}/commits/HEAD' and r.get('status')==200:
   sha=json.loads((p.parent/'body').read_text())['sha'];urls.append(f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1')
subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*urls],check=True)
