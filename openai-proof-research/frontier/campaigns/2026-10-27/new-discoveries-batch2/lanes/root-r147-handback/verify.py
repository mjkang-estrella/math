from pathlib import Path
import hashlib,json,math
from fractions import Fraction as F
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r147'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
counts={}
for name in ['finalmanifest.json','scientific-freeze.json']:
 rows=json.loads((S/name).read_text())['files']
 for r in rows:assert sha(S/r['path'])==r['sha256'],r['path']
 counts[name]=len(rows)
j=json.loads((S/'checks.json').read_text());unique={tuple(r['c']):r for d in j['degrees'] for r in d['candidates']}
verified=[];comparisons=0
for c,r in unique.items():
 d=len(c)-1;N=r['finite_N'];luc=[2,1]
 for n in range(2,N+1):luc.append(luc[-1]+luc[-2])
 for n in range(N+1):
  v=sum(x*math.comb(n,k) for k,x in enumerate(c) if k<=n)
  lim=1 if n==0 else luc[n]-(n%2==0)
  assert abs(v)<=lim,(c,n);comparisons+=1
 C=sum((F(abs(x),math.factorial(k)) for k,x in enumerate(c)),F(0))
 assert C.numerator*N**d*2**N<=C.denominator*3**N
 assert 2*(N+1)**d<=3*N**d
 verified.append({'c':list(c),'degree':d,'global_pass':True})
original=json.loads((S/'independent-checks.json').read_text())
assert verified==original['verified'] and original['all_pass']
out={'status':'PASS','hash_counts':counts,'distinct_polynomials':len(verified),'max_degree':max(r['degree'] for r in verified),'exact_prefix_comparisons':comparisons,'exact_tail_checks':2*len(verified),'matches_worker_forward_difference_audit':True,'lll_search_repeated':False,'universal_infinitude_proved':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
