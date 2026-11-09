import pathlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.body'):
 if p.read_bytes()[:4]==b'%PDF' and not p.with_suffix('.txt').exists():
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
