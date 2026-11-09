import pathlib,subprocess,json,hashlib
P=pathlib.Path(__file__).parent/'primary'
for p in P.glob('*.pdf'):
 m=json.loads(p.with_suffix('.meta.json').read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==m['sha256']
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=35)
