import pathlib,sys,json,sympy as sp,itertools
D=pathlib.Path(__file__).resolve().parents[1];sys.argv=['rsk.py','2'];ns={'__file__':str(D/'scripts/rsk.py')};exec((D/'scripts/rsk.py').read_text().split('out=[]\nfor d')[0],ns)
rows=[]
for s,p in [((1,1,1),(1,1,1)),((2,1,1),(2,1,1)),((2,1,1),(1,2,1)),((2,1,1),(1,1,2)),((1,2,1),(1,1,2))]:
 basis=ns['cont'](s,p);ix={a:i for i,a in enumerate(basis)};M=sp.zeros(len(basis))
 for j,a in enumerate(basis):
  for b,c in ns['image'](a).items():M[ix[b],j]=c
 rows.append({'s':s,'p':p,'order':len(basis),'trace':str(sp.trace(M)),'charpoly':str(sp.factor(M.charpoly().as_expr()))})
print(json.dumps(rows,indent=2));(D/'outputs/rsk-table-validation.json').write_text(json.dumps(rows,indent=2))
# Independently check normalized 78 survivors using direct ordered-difference counts,
# not the norm formula used in the initial search.
ss=json.loads((D/'outputs/dual-survivors.json').read_text());bad=[]
for S in ss:
 nu=[0]*64
 for a in S:
  for b in S:nu[(a%8-b%8)%8+8*((a//8-b//8)%8)]+=1
 for h in range(64):
  coeff=[0]*4
  for g in range(64):
   k=(g%8*(h%8)+g//8*(h//8))%8;coeff[k%4]+=(1 if k<4 else -1)*nu[g]
  if coeff[1:]!=[0,0,0] or coeff[0]%8:bad.append([S,h,coeff])
assert not bad;print('All 78 direct difference Fourier transforms are integral multiples of 8.')
