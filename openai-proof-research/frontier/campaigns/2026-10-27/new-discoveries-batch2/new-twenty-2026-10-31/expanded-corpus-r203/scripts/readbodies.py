import sys,pathlib,re,html
D=pathlib.Path(sys.argv[1])
for p in sorted((D/'sources').glob('html-*')):
 s=(p/'body').read_text();s=re.sub(r'<annotation.*?</annotation>','',s,flags=re.S);s=re.sub(r'<[^>]+>',' ',s);s=html.unescape(s);s=re.sub(r'\s+',' ',s);(p/'text.txt').write_text(s)
 print('\n'+p.name)
 for m in re.finditer(r'(?i)conjecture',s):print(s[max(0,m.start()-120):m.start()+1500])
