import pathlib,re,json
L=pathlib.Path(__file__).resolve().parent
for f in sorted((L/'sources').glob('*.txt')):
 s=f.read_text();v=re.search(r'arXiv:\S+',s)
 print('\n',f.stem,v.group() if v else 'version absent')
 ms=list(re.finditer(r'Conjecture\s+(?:\d|[A-Z])',s))
 if not ms:ms=list(re.finditer(r'conjecture',s))[-3:]
 for m in ms[:4]:print('OFFSET',m.start(),s[max(0,m.start()-80):m.start()+750])
