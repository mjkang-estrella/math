import pathlib,subprocess,re,json
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.pdf'):
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=False)
for p in (D/'sources').glob('*-abs.html'):
 t=p.read_text(); versions=re.findall(r'arXiv:([0-9.]+v[0-9]+)',t); print(p.name,sorted(set(versions)))
