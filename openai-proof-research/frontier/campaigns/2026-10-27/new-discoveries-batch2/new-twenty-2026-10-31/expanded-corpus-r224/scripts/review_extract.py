import pathlib,re,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
x=json.loads((D/'extracted.json').read_text())
for i in x:
 s=(D/'sources'/f'{i}-html.compact').read_text(); terms={
 '361496':['Conjecture 1','Conjecture 2','strongly immortal','partially immortal'],
 '361534':['zero-free region','neighborhood of zero','neighborhood of the origin','open problem'],
 '361903':['Conjecture 2','Conjecture 4','k-star','\\frac{(k+1)n}'],
 '361806':['Theorem A.5','Remark A.3','signed triangulations, weighting'],
 '371682':['Conjecture 38','Conjecture 39','planar oriented'],
 '372202':['Theorem 1','Theorem 1.1'],
 '372320':['Conjecture 1'],
 '371948':['Conjecture 9.2','q=3'],
 }.get(i,['Conjecture'])
 out=[]
 for term in terms:
  starts=[m.start() for m in re.finditer(re.escape(term),s)]
  out.extend(s[max(0,k-250):k+2000] for k in starts[:3])
 (D/'outputs'/f'{i}-focused.txt').write_text('\n\n'.join(out))
 print(i, 'sourceversions',re.findall(r'\[v\d+\]',(D/'sources'/f'{i}-abs.txt').read_text()))
