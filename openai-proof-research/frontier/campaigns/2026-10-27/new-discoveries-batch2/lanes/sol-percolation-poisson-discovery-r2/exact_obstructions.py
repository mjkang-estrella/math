"""Exact rational obstacles to two proposed black-box proof routes. NOT Conj10.2 counterexamples."""
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
from math import comb
from fractions import Fraction as F
from pathlib import Path
import hashlib,json

def main():
 N=1000;D=5000
 def tails(a):
  den=D**N
  p=[comb(N,j)*a**j*(D-a)**(N-j) for j in range(3)]
  return [den]+[den-sum(p[:j]) for j in range(1,4)]
 ta,tb=tails(12),tails(41)
 q=[ta[j]*tb[j]-ta[j+1]*tb[j+1] for j in range(3)]
 den=D**(2*N)
 defect=q[1]**2-2*q[0]*q[2]
 assert defect<0
 # Rigorously enclose the rational defect by simple rational endpoints.
 assert -F(1,10000)*den**2 < defect < -F(1,100000)*den**2
 # Merely submultiplicative and even log-concave tails need not have decreasing implied means.
 # A geometric survival t_k=2^-k: lambda1=log2; t2=1/4 > Phi2(log2)=(1-log2)/2
 # because log2>1/2, from integral_1^2 1/x dx>1/2.
 out=dict(status='uncredited exact route obstructions, NOT a target counterexample',finite_simple_graph=dict(vertices=2*N+3,edges=4*N,description='terminals s,t and hub h; for i=1..N private u_i,v_i; s-u_i probability12/5000,u_i-h probability1,h-v_i probability41/5000,v_i-t probability1',flow='min(Bin(1000,12/5000),Bin(1000,41/5000)), independent'),pmf=[float(F(v,den)) for v in q],ulc_required='q1^2 >= 2*q0*q2',defect_enclosure=['-1/10000','-1/100000'],defect_numerator_negative=defect<0,defect_numerator_bits=abs(defect).bit_length(),defect_numerator_hex_sha256=hashlib.sha256(hex(defect).encode()).hexdigest(),maxrss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
 (Path(__file__).resolve().parent/'exact-obstructions.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
