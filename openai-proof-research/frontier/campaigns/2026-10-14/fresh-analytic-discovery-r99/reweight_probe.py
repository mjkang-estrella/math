#!/usr/bin/env python3
"""Exact signed Table-I perturbation using stipulated frozen Gram remainder.
Not a new Gram search or a full mathematical verifier. Original wrapper MIT.
Copies source engines into a temporary directory; source packet is read-only.
"""
import hashlib,json,sys,tempfile,shutil,importlib.util
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
root=Path(__file__).resolve().parent
base=root/'private/preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/verification'
receipts={x['path']:x for x in json.loads((root/'source367-receipts.json').read_text())}
for p in [base/'independent-certificate/engine.py',base/'independent-certificate/bounds.py',base/'independent-certificate/output/coefficients.json',base/'checks/original/certificate-inputs.txt']:
 rel=str(p.relative_to(root/'private'));assert hashlib.sha256(p.read_bytes()).hexdigest()==receipts[rel]['sha256']
tmp=Path(tempfile.mkdtemp(prefix='r99-reweight-',dir='/var/tmp'))
for name in ['engine.py','bounds.py']:shutil.copyfile(base/'independent-certificate'/name,tmp/name)
sys.dont_write_bytecode=True;sys.path.insert(0,str(tmp))
import engine as e
import bounds as b
e.self_checks();b.self_check()
rows,blocks,prefix=e.input_tables(base/'checks/original/certificate-inputs.txt')
def table(a):
 e.AEXP=a;o=defaultdict(F)
 for name,key,n in rows:
  for k,v in e.row_interior(name,key).items():
   if k[0]==0 and k[2]==0:o[k]+=F(n,e.Q)*v
 return e.clean(o)
a0=F(29,50);old=table(a0)
original={}
for x in json.loads((base/'independent-certificate/output/coefficients.json').read_text()):
 h,w,z,tr,ed=x['key'];k=(h,w,z,tuple(tr),tuple(tuple(y) for y in ed))
 if h==0 and z==0:original[k]=F(x['scaled_coefficient'],e.Q**2)
def determinant(a):
 if len(a)==1:return a[0][0]
 return sum((-1)**j*a[0][j]*determinant([row[:j]+row[j+1:] for row in a[1:]]) for j in range(len(a)))
results=[]
for t in [F(0),F(1,500000),F(1,100000),F(1,1000),F(17,100),F(18,100),F(43,100)]:
 new=table(a0+t);keys=set(original)|set(old)|set(new)
 rem={k:original.get(k,F(0))-new.get(k,F(0))+old.get(k,F(0)) for k in keys}
 summary=b.summarize(rem);D=[[F(0) for _ in range(4)] for _ in range(4)]
 for x in summary['pairs']:
  i,j=x['pair'];D[i-1][j-1]=D[j-1][i-1]=F(x['scaled_entry'],summary['matrix_scale'])
 diag=[F(2,25),F(2,25),F(1,4),F(1)];inds=[0,2,3]
 C=[[diag[i]*(i==j)-D[i][j] for j in inds] for i in inds]
 minors=[determinant([row[:n] for row in C[:n]]) for n in [1,2,3]]
 results.append({'t':str(t),'a_prime':str(a0+t),'remaining_keys':summary['nonzero_key_count'],'leading_minors':[str(x) for x in minors],'positive_definite':all(x>0 for x in minors),'comparison_matrix':[[str(x) for x in row] for row in C]})
assert results[0]['positive_definite']
receipt={'scope':'Signed reweighting, g=z=0, original stipulated Gram remainder, exact graph magnitude bounds; failure is not an inequality counterexample.','results':results}
p=tmp/'receipt.json';p.write_text(json.dumps(receipt,indent=2)+'\n');print(p);print(hashlib.sha256(p.read_bytes()).hexdigest());print(json.dumps(results,indent=2))
