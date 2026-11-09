import runpy,json,pathlib,itertools
# Reproduce definition-driven minimal-codeword counts for small multiplicities without the polynomial.
m=runpy.run_path('scripts/codes.py');val=m['val'];pred=m['pred']
def direct(a):
 rows=[i for i,x in enumerate(a) for _ in range(x)];k=len(rows);words=[]
 for s in range(1,1<<k):
  x=0
  for j in range(k):
   if s>>j&1:x^=rows[j]
  words.append(s|(x<<k))
 return sum(not any(t!=w and t&w==t for t in words) for w in words)
checks=[]
for a in [[0,1,1,0,1,0,0,1],[0,0,1,1,1,1,0,0],[0,1,2,0,1,0,0,1],[0,0,0,1,1,1,1,0]]:
 d=direct(a);v=val(a);assert d==v;checks.append({'a_bit_indexed':a,'direct':d,'polynomial':v})
rows=[]
for k in [27,28,29,30,100,150,151,1000]:
 a=[0]*8
 for t,j in zip([4,2,1,7],range(4)):a[t]=(k+j)//4
 rows.append({'k':k,'printed_a':pred(k),'printed_value':val(pred(k)),'source_Proposition_3_11_a':a,'source_construction_value':val(a)})
pathlib.Path('outputs/codes-bridge.json').write_text(json.dumps({'checks':checks,'source_bridge':rows,'decision':'No discovery claim: printed conjecture conflicts with source-own explicit construction and reported checked range.'},indent=2))
print(json.dumps(rows,indent=2))
