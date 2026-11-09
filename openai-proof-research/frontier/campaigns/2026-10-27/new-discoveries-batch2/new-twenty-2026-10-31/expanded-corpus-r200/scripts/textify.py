import pathlib,json,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*/receipt.json'):
 r=json.loads(p.read_text());b=p.parent/'body'
 if r.get('status')==200 and b.read_bytes().startswith(b'%PDF') and not (p.parent/'body.txt').exists():
  subprocess.run(['pdftotext','-layout',str(b),str(p.parent/'body.txt')],check=True)
