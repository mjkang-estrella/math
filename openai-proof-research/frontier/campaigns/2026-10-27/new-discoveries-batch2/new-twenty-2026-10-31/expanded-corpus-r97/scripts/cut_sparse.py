import pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n,p in [(34,3),(40,3),(48,3),(34,4),(40,4)]:
 full=(1<<n)-1;non=[]
 for i in range(n):non.append(sum(1<<j for j in range(n) if i!=j and min((i-j)%n,(j-i)%n)>p))
 fs={}
 def visit(S,avail,forbid):
  fs.setdefault(S.bit_count(),[]).append(S)
  while avail:
   b=avail&-avail;avail^=b;v=b.bit_length()-1
   if forbid&b:continue
   F=forbid;t=S&non[v]
   while t:
    c=t&-t;t^=c;u=c.bit_length()-1;F|=non[v]&non[u]
   visit(S|b,avail&~F,F)
 visit(0,full,0)
 ranks={0:0}
 for size in sorted(fs)[1:]:
  rows={x:i for i,x in enumerate(fs[size-1])};piv={}
  for s in fs[size]:
   col=0;t=s
   while t:b=t&-t;t^=b;col^=1<<rows[s^b]
   while col:
    lead=col.bit_length()-1
    if lead not in piv:piv[lead]=col;break
    col^=piv[lead]
  ranks[size]=len(piv)
 betti={str(s-1):len(fs[s])-ranks[s]-ranks.get(s+1,0) for s in fs}
 row={'n':n,'p':p,'k':3,'faces':sum(map(len,fs.values())),'face_counts':{str(s-1):len(fs[s]) for s in fs},'reduced_mod2_betti':betti};out.append(row);(D/'outputs/cut-sparse.json').write_text(json.dumps(out,indent=2)+'\n');print(row,flush=True)
