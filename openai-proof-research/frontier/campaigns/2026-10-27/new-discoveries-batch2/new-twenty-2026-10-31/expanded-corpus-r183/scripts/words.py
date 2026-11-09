from pathlib import Path
import sys,json
D=Path(__file__).resolve().parents[1];k=int(sys.argv[1]);bound=int(sys.argv[2]);counts=[0]*(bound+1);ext=[0]*(bound+1);witness={}
def suffix_ok(w):return not any(w[-2*j:-j]==w[-j:] for j in range(1,len(w)//2+1))
def sqfree(w):return all(w[i:i+j]!=w[i+j:i+2*j] for j in range(1,len(w)//2+1) for i in range(len(w)-2*j+1))
def extremal(w):
 # A previously unused letter immediately gives a valid extension.
 if len(set(w))<k:return False
 for i in range(len(w)+1):
  for c in range(k):
   if (i and w[i-1]==c) or (i<len(w) and w[i]==c):continue
   if sqfree(w[:i]+bytes([c])+w[i:]):return False
 return True
def visit(w,used):
 n=len(w);counts[n]+=1
 if extremal(w):
  ext[n]+=1;witness.setdefault(n,list(w))
 if n==bound:return
 for c in range(min(k,used+1)):
  v=w+bytes([c])
  if suffix_ok(v):visit(v,max(used,c+1))
visit(b'',0)
r={'alphabet_size':k,'max_length':bound,'symmetry':'restricted-growth words; exactly one representative per alphabet-permutation orbit','squarefree_representatives_by_length':counts,'extremal_representatives_by_length':ext,'witnesses':witness,'scope':'P=XX only; cannot settle the quantified all-pattern/all-alphabet statement'}
(D/f'outputs/words-{k}.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
