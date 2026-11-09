import pathlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((D/'sources').glob('*pdf.body')):
 if p.read_bytes()[:4]!=b'%PDF':continue
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=15)
