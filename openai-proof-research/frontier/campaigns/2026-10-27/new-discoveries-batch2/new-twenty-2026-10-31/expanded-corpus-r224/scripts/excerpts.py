import pathlib,re,json
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*-html.txt'):
 s=re.sub(r'\s+',' ',p.read_text());(p.with_suffix('.compact')).write_text(s)
 snippets=[]
 for m in re.finditer(r'(?i)conjecture',s):snippets.append(s[max(0,m.start()-160):m.start()+1500])
 (D/'outputs'/(p.stem+'-conjectures.txt')).write_text('\n\n'.join(snippets))
 print(p.stem, len(s),len(snippets))
