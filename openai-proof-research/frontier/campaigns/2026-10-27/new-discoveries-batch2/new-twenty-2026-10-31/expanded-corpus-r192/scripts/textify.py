import pathlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*-v*.body'):
 if p.read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
