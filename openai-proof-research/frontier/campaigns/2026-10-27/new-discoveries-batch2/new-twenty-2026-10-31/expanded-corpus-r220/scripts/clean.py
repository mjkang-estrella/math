import pathlib,re
L=pathlib.Path(__file__).resolve().parents[1]
for p in (L/'outputs').glob('*-html.txt'):
 s=p.read_text();s=re.sub(r'\$[^$]*?\\pgfpicture.*?\\endpgfpicture[^$]*?\$', ' [diagram-symbol] ',s,flags=re.S)
 (L/'outputs'/p.name.replace('-html','-clean')).write_text(s)
