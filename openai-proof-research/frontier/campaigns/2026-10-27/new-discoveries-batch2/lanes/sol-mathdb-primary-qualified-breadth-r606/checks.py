from pathlib import Path
from fractions import Fraction
from math import prod,factorial
import json
out=[]
for t in range(2,13):
 b=prod(2**t-2**i for i in range(t));f=Fraction(b,factorial(t+1)*(2**t-1)**(t+1));g=Fraction(1,(t+1)**(t+1))
 out.append({'t':t,'ordered_bases':b,'uniform_F_k1':str(f),'projective_F_k1':str(g),'ratio':str(f/g),'uniform_strictly_better':f>g})
D=Path(__file__).parent;(D/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
