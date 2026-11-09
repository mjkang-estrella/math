"""Independent exact check of the r=1 Wakhare/Yuster relation at samples."""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json,hashlib
from check_signs import eval_source,lo,hi
K=48
def h(k,r,x):
 return sum(x**(r*j)*sum(Q((-1)**(j-v),v+1)*comb(r*v+k,k)*comb(k,j-v) for v in range(j+1)) for j in range(k))
rows=[]
for x in [Q(1,100),Q(1,10),Q(1,2),Q(3,5),Q(4,5)]:
 rho,sigma=eval_source(K,x)
 hw,h1=h(K,K,x),h(K,1,x)
 factor=Q((-1)**(K+1),K)*(1-x)**K
 assert K*(1-x)**K*hw==factor*rho
 assert (1-x**K)**K*h1==factor*sigma
 rows.append({'x':str(x),'factor':str(factor),'rho_identity':True,'sigma_identity':True})
p=Path(__file__).resolve().parent/'wakhare-relation-check.json';p.write_text(json.dumps({'relation':'p_W(k,1)=(-1)^(k+1)/k*(1-x)^k*p_Y(k)','k':K,'method':'independently evaluate exact Eq1.3 binomial sums and literal Yuster Cor3.7 sums','rows':rows},indent=2)+'\n');print('WAKHARE PASS',hashlib.sha256(p.read_bytes()).hexdigest())
