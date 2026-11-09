import pathlib,subprocess,re,json
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.pdf'):
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
for p in sorted((D/'sources').glob('*.abs')):
 t=p.read_text(); v=re.findall(r'arxiv.org/(?:abs|pdf)/([^"<> ]+v\d+)',t)
 h=re.findall(r'\[v\d+\].{0,160}',t)
 print(p.stem,'versions',sorted(set(v)),h)
