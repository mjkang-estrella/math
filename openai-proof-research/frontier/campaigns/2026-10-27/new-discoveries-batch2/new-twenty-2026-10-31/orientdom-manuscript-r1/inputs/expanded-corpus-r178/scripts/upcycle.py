import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];good=[]
for bits in itertools.product('01',repeat=6):
 it=iter(bits);w=''.join('*' if i%4==0 else next(it) for i in range(8));seen=[]
 for i in range(8):
  window=''.join(w[(i+j)%8] for j in range(4))
  for v in '01':seen.append(window.replace('*',v))
 if len(set(seen))==16:good.append(w)
(D/'outputs/upcycle.json').write_text(json.dumps({'n':4,'diamond_positions':[0,4],'binary_assignments':64,'solutions':good,'scope':'all rotation-normalized templates for n=4,d=1; no n>=16 claim'},indent=2));print(good)
