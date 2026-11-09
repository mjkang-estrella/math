"""Independent lane regression. No imported campaign scripts. Run with python3 -I."""
import json, math, itertools, collections, pathlib
lane=pathlib.Path(__file__).resolve().parent.parent
ref=json.loads((lane.parent/'expanded-corpus-r133/outputs/stack_pairs_P_1_82.json').read_text())
def sort(w):
 if not w:return ()
 m=max(w);i=w.index(m)
 return sort(w[:i])+sort(w[i+1:])+(m,)
def badsort(w):
 if not w:return ()
 m=max(w);i=w.index(m)
 return (m,)+badsort(w[:i])+badsort(w[i+1:])
for n in range(9):
 cnt=collections.Counter(sort(w) for w in itertools.permutations(range(n)))
 p=sum(v*v for v in cnt.values())
 assert p==int(ref.get(str(n),1))
 print('literal',n,p,flush=True)
# Full (unpruned) top-maximum table, additive identities checked before subtraction.
X=[{(0,0):1}];I=[{}];mu=[1,2,1]
for M in range(1,21):
 xm={};im={}
 for r in range(1,M+1):
  for s in range(1,M+1):
   ki=sum(mu[t]*mu[u]*X[M-1].get((r-1+t,s-1+u),0) for t in range(3) for u in range(3))
   c1=c2=0
   for b in range(1,M):
    cv=sum(X[M-b].get((r-v,s-w),0)*I[b].get((v,w),0) for v in range(1,r) for w in range(1,s))
    c1+=math.comb(M-1,b-1)*cv;c2+=math.comb(M,b)*cv
   assert c1<=ki
   im[r,s]=ki-c1;xm[r,s]=im[r,s]+c2
 X.append(xm);I.append(im)
 assert xm[1,1]==int(ref[str(M)])
 print('topmax',M,xm[1,1],flush=True)
G=[1]+[X[n][1,1] for n in range(1,21)]
for n in range(21,131):
 G.append(4*G[n-1]+sum(math.comb(n-1,i)*G[i]*G[n-1-i] for i in range(1,n-1)))
assert all(G[n]<=int(ref[str(n)]) for n in range(1,83))
def cert(a,q): return G[a]*100**(a+1)>4*(a+1)*math.factorial(a)*q**(a+1)
assert cert(130,173) and not cert(129,173) and not cert(130,195)
assert X[5][1,1]!=2357
assert badsort((4,1,6,3,5,2))!=sort((4,1,6,3,5,2))
(lane/'numeric.json').write_text(json.dumps({'G':[str(v) for v in G], 'negative_controls':{'wrong_seed':True,'base129_fails':True,'threshold195_fails':True,'wrong_convention':True}},indent=2)+'\n')
(lane/'StackSortCertificate.lean').write_text('''import StackSortBasic
noncomputable section
namespace StackSort
/-- Literal result of the untrusted lower recursion; linkage remains a separate proposition. -/
def lower130 : ℕ := '''+str(G[130])+'''
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem certificate130 :
    4 * 131 * Nat.factorial 130 * 173 ^ 131 < lower130 * 100 ^ 131 := by decide
end StackSort
''')
print('base 130 certificate PASS; four negative controls PASS')
