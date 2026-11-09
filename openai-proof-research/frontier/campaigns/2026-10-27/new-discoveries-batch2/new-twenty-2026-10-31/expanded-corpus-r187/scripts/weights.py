import pathlib,json,functools
D=pathlib.Path(__file__).resolve().parents[1]
@functools.lru_cache(None)
def gb(q,n,k):
 if k<0 or k>n:return 0
 if k==0 or k==n:return 1
 return gb(q,n-1,k)+q**(n-k)*gb(q,n-1,k-1)
def weights(q,l,m,t):
 # Common mu_s term cancels in comparisons, so use negative Krawtchouk sums.
 return [-sum(sum((-1)**(s-i)*q**(i*m+(s-i)*(s-i-1)//2)*gb(q,l-i,l-s)*gb(q,l-r,i) for i in range(s+1)) for s in range(1,t+1)) for r in range(1,l+1)]
hits=[];cnt=0;last=None
for q in [2,3,4,5,7,8,9]:
 for l in range(3,31):
  for m in range(l,l+7):
   for t in range(2,l):
    w=weights(q,l,m,t);cnt+=1
    ok=len(set(w))==l and all(w[j]<w[j+1] for j in range(l-t)) and all(min(w[j-2:j])<w[j]<max(w[j-2:j]) for j in range(l-t+1,l))
    if not ok:
     h={'q':q,'ell':l,'m':m,'t':t,'relative_weights':w};hits.append(h);print('HIT',h,flush=True)
  last=(q,l);print('complete',q,l,cnt,flush=True)
(D/'outputs/weights.json').write_text(json.dumps({'cases':cnt,'q':[2,3,4,5,7,8,9],'ell':[3,30],'m_offsets':[0,6],'t':'2..ell-1','hits':hits},indent=2))
