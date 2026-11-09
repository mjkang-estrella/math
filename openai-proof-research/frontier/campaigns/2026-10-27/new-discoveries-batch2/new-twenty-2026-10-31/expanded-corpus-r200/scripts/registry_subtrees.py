import pathlib,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];urls=[]
for p in (D/'sources').glob('*/receipt.json'):
 r=json.loads(p.read_text())
 if '/git/trees/' not in r['url'] or '?' in r['url'] or r.get('status')!=200:continue
 repo='openai/math' if 'openai/math' in r['url'] else 'the-omega-institute/trureturing'
 for x in json.loads((p.parent/'body').read_text())['tree']:
  if x['path'] in ['preprints','Problems','D5'] and x['type']=='tree':
   url=f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1'
   if not any(json.loads(p.read_text())['url']==url for p in (D/'sources').glob('*/receipt.json')):urls.append(url)
subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*urls],check=True)
