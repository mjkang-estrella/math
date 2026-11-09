import pathlib,subprocess,json,re
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.pdf'):
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=False)
for p in (D/'sources').glob('*.abs.html'):
 t=p.read_text(); print(p.name,re.findall(r'\[v\d+\].{0,100}',t))
