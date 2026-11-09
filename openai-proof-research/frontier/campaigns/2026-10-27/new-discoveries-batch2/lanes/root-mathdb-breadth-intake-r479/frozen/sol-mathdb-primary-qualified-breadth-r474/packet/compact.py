import pathlib,re,sys
O=pathlib.Path(__file__).resolve().parents[1];files=sorted(p for p in (O/'sources').glob('*.txt') if not p.name.startswith('passages-'))
for p in files[int(sys.argv[1]):int(sys.argv[2])]:
 ls=p.read_text().splitlines();ix=[i for i,l in enumerate(ls) if re.match(r'^\s*(Conjecture|Theorem 1\.|Question|Problem)\s*\d',l)];print('\n'+p.name+' VERSION '+' '.join(l.strip() for l in ls[:60] if 'arXiv' in l));
 for i in ix[:5]:print('\n'.join(f'{j+1}: {ls[j]}' for j in range(i,min(i+9,len(ls)))))
