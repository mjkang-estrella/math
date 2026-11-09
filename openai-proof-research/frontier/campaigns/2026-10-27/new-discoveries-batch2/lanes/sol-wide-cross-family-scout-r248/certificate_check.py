import pathlib,json,itertools
from attractor_checks import close,theta
L=pathlib.Path(__file__).resolve().parent
w='010110010101100101101001101010011010'
x='';stages=[];suffixes=[]
for a,e in [('0',1),('0',1),('1',1),('0',1),('1',0)]:
 y=x+a;suffixes.append(max(k for k in range(len(y)+1) if y[len(y)-k:]==theta(y[len(y)-k:],e)))
 x=close(y,e);stages.append(x)
assert x==w and suffixes==[0,2,0,4,2] and w==w[::-1]
expected={'001010':[(5,10)],'010101':[(6,11)],'101011':[(7,12)],'001011':[(13,18)],'101101':[(15,20)],'110100':[(17,22)],'110101':[(23,28)],'101010':[(24,29)],'010100':[(25,30)],'1100':[(3,6),(11,14)],'0011':[(21,24),(29,32)]}
for f,ints in expected.items():
 actual=[(i,i+len(f)-1) for i in range(len(w)-len(f)+1) if w[i:i+len(f)]==f]
 assert actual==ints,(f,actual)
constraints=[set().union(*(set(range(a,b+1)) for a,b in ints)) for ints in expected.values()]
assert not any(all(set(c)&r for r in constraints) for c in itertools.combinations(range(36),4))
g={5,10,18,21,28};nf=0
for length in range(1,37):
 for f in {w[i:i+length] for i in range(37-length)}:
  assert any(w[i:i+length]==f and any(i<=p<i+length for p in g) for i in range(37-length));nf+=1
out=dict(pass_check=True,stages=stages,longest_suffix_lengths=suffixes,eleven_factor_occurrences=expected,four_subsets=58905,five_attractor=sorted(g),distinct_factors=nf)
(L/'certificate-receipt.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
