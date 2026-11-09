import pathlib,re
L=pathlib.Path(__file__).resolve().parents[1];out=[]
for p in sorted((L/'sources').glob('*-pdf/text.txt')):
 ls=p.read_text().splitlines();hits=[i for i,s in enumerate(ls) if re.match(r'^Conjecture|^Problem|^Question',s)]
 out.append('\n### '+p.parent.name)
 for i in hits:out.extend(ls[max(0,i-3):i+13])
(L/'evidence/source-conjectures.txt').write_text('\n'.join(out))
print('\n'.join(out))
