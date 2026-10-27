#!/usr/bin/env python3
"""Independent exact verification of the public prior witness; no novelty credit."""
import sympy as s
import json
from pathlib import Path

A=s.Matrix([[9,0,2,0],[0,2,1,0],[2,1,1,0],[0,0,0,1]])
P=s.diag(1,1,0,0)
Y=s.Matrix([[0,0,0,0],[0,0,0,0],[1,0,0,0],[0,1,0,0]])
m=s.Rational(1,25); M=s.Integer(13); I=s.eye(4)
L=s.Matrix([[1,0,0,0],[0,1,0,0],[s.Rational(25,112),s.Rational(25,49),1,0],[0,0,0,1]])
U=s.Matrix([[1,0,0,0],[0,1,0,0],[-s.Rational(1,2),-s.Rational(1,11),1,0],[0,0,0,1]])
assert A-m*I == L*s.diag(s.Rational(224,25),s.Rational(49,25),s.Rational(33,9800),s.Rational(24,25))*L.T
assert M*I-A == U*s.diag(4,11,s.Rational(120,11),12)*U.T
assert P.T*Y == s.zeros(4)
assert P*P.T*P == P and Y*Y.T*Y == Y
phi=lambda Z:P*Z*P.T+Y*Z*Y.T
assert phi(I)==I
D=phi(P.T*A*P); E=phi(Y.T*A*Y); C=phi(P.T*A*Y)
assert D==s.diag(9,2,9,2) and E==I
G=C*E.inv()*C.T*D.inv()
block=s.Matrix([[s.Rational(4,9),1],[s.Rational(2,9),s.Rational(1,2)]])
assert G==s.diag(block,block)
q=((M-m)/(M+m))**2
assert q==s.Rational(26244,26569)
v=I[:,1]; norm_sq=(G*v).dot(G*v)
assert norm_sq==s.Rational(5,4) and norm_sq>q**2
result={'status':'PASS exact public-prior witness; credit0','norm_sq':str(norm_sq),
        'claimed_bound':str(q),'squared_gap':str(norm_sq-q**2),
        'map':'Phi(Z)=P Z P* + Y Z Y*; unital Kraus map, hence completely positive',
        'prior_commit':'494409d280d86df6842778425e3ed3f6c9af5dbc'}
out=json.dumps(result,indent=2)+'\n'
Path(__file__).with_name('exact-check.json').write_text(out)
print(out,end='')
