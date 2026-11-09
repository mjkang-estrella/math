import pathlib,json,subprocess,sys,re
D=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((D/'reservation.json').read_text())['rows']
mode=sys.argv[1]
urls=[]
if mode=='abs':
 done={json.loads(p.read_text())['url'] for p in (D/'sources').glob('*/receipt.json')}
 urls=[x['source_url'] for x in rows if x['source_url'] not in done]
if mode=='pdf':urls=[x['source_url'].replace('/abs/','/pdf/') for x in rows]
if mode=='pool':
 head=next(json.loads((p.parent/'body').read_text())['sha'] for p in (D/'sources').glob('*/receipt.json') if 'lean-pool/commits/HEAD' in p.read_text())
 urls=[f'https://raw.githubusercontent.com/Vilin97/lean-pool/{head}/projects.yml',f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{head}?recursive=1']
subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*urls],check=True)
