"""Exact finite admissible-power diagnostics; stdout only, run with python -B."""
import sys, json, runpy
from pathlib import Path
from math import gcd, lcm, comb
ROOT=Path(__file__).resolve().parents[3]
old=runpy.run_path(str(ROOT/'frontier/experiments/i104_modular_representation_discovery/diagnostics.py'))

def affine(l,d):
 r=next(r for r in range(1,l) if pow(r,d,l)==1 and all(pow(r,j,l)!=1 for j in range(1,d)))
 es=[(a,b) for b in range(d) for a in range(l)]; ix={x:i for i,x in enumerate(es)}
 tab=[[ix[((a+pow(r,b,l)*c)%l,(b+e)%d)] for c,e in es] for a,b in es]
 return finish(tab)

def finish(tab):
 N=len(tab); inv=[next(j for j in range(N) if tab[i][j]==0) for i in range(N)]; orders=[]
 for i in range(N):
  v=i;o=1
  while v:v=tab[v][i];o+=1
  orders.append(o)
 return tab,inv,orders

def product(g,k):
 tab,_,_=g; N=len(tab)
 return finish([[tab[i//k][j//k]*k+(i+j)%k for j in range(N*k)] for i in range(N*k)])

def classes(tab,inv):
 unseen=set(range(len(tab))); out=[]
 while unseen:
  g=min(unseen); cl={tab[tab[x][g]][inv[x]] for x in range(len(tab))};out.append(cl);unseen-=cl
 return out

def compositions(n,r):
 if r==1:yield (n,);return
 for a in range(n+1):
  for v in compositions(n-a,r-1):yield (a,)+v

def vp(x,p,cap):
 if x==0:return cap
 v=0
 while x%p==0:v+=1;x//=p
 return v

def search(name,g,p,max_s,h=8,all_a=True):
 tab,inv,orders=g; N=len(tab); exp=lcm(*orders);ep=exp
 while ep%p==0:ep//=p
 pp=exp//ep
 period=1
 while pow(p,period,ep)!=1%ep:period+=1
 aa=list(range(1,period+1)) if all_a else [1]
 hs=old['subgroups'](tab)
 normals=[H for H in hs if all({tab[tab[x][z]][inv[x]] for z in H}==H for x in range(N))]
 assert all(len(H)==1 or any(orders[x]%p!=0 for x in H if x) for H in normals), 'nontrivial p-core'
 cs=[C for C in classes(tab,inv) if orders[next(iter(C))]%p==0]
 assert cs
 mus=[0]*len(hs);mus[-1]=1
 for i in range(len(hs)-2,-1,-1):mus[i]=-sum(mus[j] for j in range(i+1,len(hs)) if hs[i]<hs[j])
 Z=sum(all(tab[x][y]==tab[y][x] for y in range(N)) for x in range(N)); orbit=N//Z;mod=orbit*p**h
 data=[]
 for H,mu in zip(hs,mus):
  if not mu:continue
  li=sorted(H);pos={x:i for i,x in enumerate(li)};ht=[[pos[tab[x][y]] for y in li] for x in li]
  ws=[[int(x in C) for x in li] for C in cs]
  def conv(a,b):
   z=[0]*len(li)
   for i,ai in enumerate(a):
    if ai:
     for j,bj in enumerate(b):
      if bj:z[ht[i][j]]=(z[ht[i][j]]+ai*bj)%mod
   return z
  powers=[]
  for w in ws:
   pw=[[1]+[0]*(len(li)-1)]
   for n in range(p**max_s):pw.append(conv(pw[-1],w))
   powers.append(pw)
  handles=[]
  for a in aa:
   t=next(v for v in range(1,exp+1) if v%pp==1%pp and v%ep==pow(p,a,ep))
   hv=[0]*len(li)
   for x in li:
    for y in li:
     yt=0
     for _ in range(t%orders[y]):yt=tab[yt][y]
     hv[pos[tab[tab[tab[x][y]][inv[x]]][inv[yt]]]]+=1
   handles.append((a,t,hv))
  data.append((mu,ht,powers,handles))
 out=[]
 for s in range(max_s+1):
  n=p**s; rows=[]
  for counts in compositions(n,len(cs)):
   multi=1;left=n
   for c in counts:multi*=comb(left,c);left-=c
   totals=[0]*len(aa)
   for mu,ht,powers,handles in data:
    vec=powers[0][counts[0]]
    for j in range(1,len(cs)):
     b=powers[j][counts[j]];z=[0]*len(vec)
     for u,vu in enumerate(vec):
      if vu:
       for v,bv in enumerate(b):
        if bv:z[ht[u][v]]=(z[ht[u][v]]+vu*bv)%mod
     vec=z
    for j,(_,_,hv) in enumerate(handles):totals[j]=(totals[j]+mu*multi*sum(x*y for x,y in zip(vec,hv)))%mod
   assert all(x%orbit==0 for x in totals)
   rows.append({'multiset':counts,'residues':[x//orbit for x in totals]})
  out.append({'s':s,'n':n,'multisets':len(rows),'minimum_vp_capped':[min(vp(r['residues'][j],p,h) for r in rows) for j in range(len(aa))],'rows':rows})
 return {'group':name,'order':N,'p':p,'a':aa,'t':[next(v for v in range(1,exp+1) if v%pp==1%pp and v%ep==pow(p,a,ep)) for a in aa],'p_core':1,'subgroups':len(hs),'class_sizes':[len(c) for c in cs],'modulus':p**h,'results':out}

def main():
 cases=[('S3',old['group'](3),2,10),('A5',old['group'](5,True),2,10),('A5',old['group'](5,True),3,5),('A5',old['group'](5,True),5,4),('S4',old['group'](4),3,5),('D14',affine(7,2),2,9),('F21',affine(7,3),3,5),('F39',affine(13,3),3,4),('S3xC3',product(old['group'](3),3),2,5)]
 result={'boundary':'finite exact modular evidence, not a universal proof','cases':[]}
 for args in cases:
  row=search(*args);result['cases'].append(row)
 print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
