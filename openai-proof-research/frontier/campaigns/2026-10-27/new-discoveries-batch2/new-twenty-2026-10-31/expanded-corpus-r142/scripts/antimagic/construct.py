# Explicit construction (ordinary proof in outputs/antimagic/proof.md) of a local antimagic
# labeling of the complete full t-ary tree T(t,n) (t even, n levels) with exactly l+1 colours.
# Returns: parent array, list of (child, label) for edges. Vertices: rows, BFS order.
def tree(t,n):
  rows=[[0]]; par=[-1]; nxt=1
  for h in range(1,n+1):
    row=[]
    for u in rows[-1]:
      for _ in range(t): par.append(u); row.append(nxt); nxt+=1
    rows.append(row)
  return rows,par
def children(rows,t,h,j):  # j-th vertex of row h -> its children in row h+1
  return rows[h+1][j*t:(j+1)*t]
def construct(t,n):
  assert t%2==0 and t>=2 and n>=1
  rows,par=tree(t,n); lab={}  # lab[child vertex] = label of edge to parent
  m=sum(t**h for h in range(1,n+1))
  if n==1:
    for i,v in enumerate(rows[1]): lab[v]=i+1
    return rows,par,lab
  if n==2:
    if t==2:
      # explicit: root edges 1,4; vertex(1): leaves 2,3; vertex(4): leaves 6,5
      a,b=rows[1]; lab[a]=1; lab[b]=4
      la=children(rows,t,1,0); lb=children(rows,t,1,1)
      lab[la[0]]=2; lab[la[1]]=3; lab[lb[0]]=6; lab[lb[1]]=5
      return rows,par,lab
    M=t+t*t; h2=t//2
    R_rest=list(range(h2+3,3*h2+2))        # t-1 consecutive root labels
    rstar=2
    Sstar=[1]+list(range(3,h2+3))+list(range(3*h2+2,2*t+1))
    assert len(R_rest)==t-1 and len(Sstar)==t
    B=list(range(2*t+1,M+1))               # t(t-1) consecutive leaf labels
    # Lemma 2.13 (source): partition B (t blocks of size n'=t-1, n' odd) into t-tuples with consecutive sums
    npr=t-1; blocks=[B[i*npr:(i+1)*npr] for i in range(t)]
    tuples=[[] for _ in range(npr)]
    for i in range(h2-1):
      for j in range(npr): tuples[j]+= [blocks[i][j], blocks[t-1-i][npr-1-j]]
    mid=blocks[h2-1]+blocks[h2]            # 2n' consecutive, n'=2kk+1 -> Lemma 2.2
    kk=(npr-1)//2; base=mid[0]-1
    pairs=[(2*i+1,3*kk+2-i) for i in range(kk+1)]+[(2*i,4*kk+3-i) for i in range(1,kk+1)]
    pairs.sort(key=lambda p:p[0]+p[1])     # sums 3kk+3 .. 5kk+3 consecutive
    for j,(a,b) in enumerate(pairs): tuples[j]+=[base+a,base+b]
    tuples.sort(key=sum)
    mids=rows[1]
    lab[mids[0]]=rstar
    for v,x in zip(children(rows,t,1,0),Sstar): lab[v]=x
    for idx,(r,tup) in enumerate(zip(sorted(R_rest,reverse=True),tuples)):
      v=mids[idx+1]; lab[v]=r
      for w,x in zip(children(rows,t,1,idx+1),tup): lab[w]=x
    return rows,par,lab
  # n>=3: Plan A
  q=t**(n-1); k=q//2; N=sum(t**h for h in range(1,n)); Rr=(N-t)//2; Z=Rr+1
  # sigma on [1,q]: sigma(a)=2a (a<=k), sigma(k+j)=2j-1
  sigma={a:2*a for a in range(1,k+1)}; sigma.update({k+j:2*j-1 for j in range(1,k+1)})
  # leaf tuples from [N+1,N+tq]: t blocks of size q
  blocks=[list(range(N+1+b*q,N+1+(b+1)*q)) for b in range(t)]
  h2=t//2; tuples={}
  for a in range(1,q+1):
    tup=[]
    for i in range(h2-1): tup+=[blocks[i][a-1],blocks[t-1-i][q-a]]
    base=N+(h2-1)*q
    tup+=[base+a, base+2*q+1-sigma[a]]
    tuples[a]=tup
  Msum=sum(tuples[1])-(1-sigma[1])  # tuple sum = Msum + (a-sigma(a))
  c=Msum+Z
  # level sets: E (level n-1) distances 1..k; shells for levels n-2..2 outward; A1 = {Z} u [N-t+2,N]
  dist={}; d0=k
  dist[n-1]=list(range(1,k+1))
  for h in range(n-2,1,-1):
    sz=t**h//2; dist[h]=list(range(d0+1,d0+sz+1)); d0+=sz
  assert d0==Rr, (d0,Rr)
  A1=[Z]+list(range(N-t+2,N+1))
  # assign: row h vertex j gets children labels = t/2 symmetric pairs from level h+1 distance list
  # level 1 labels: A1 in order over rows[1]
  for v,x in zip(rows[1],A1): lab[v]=x
  for h in range(1,n-1):   # children of row h are level h+1 edges
    ds=dist[h+1]; per=t//2
    for j,u in enumerate(rows[h]):
      mine=ds[j*per:(j+1)*per]; labs=[]
      for d in mine: labs+=[Z-d,Z+d]
      for w,x in zip(children(rows,t,h,j),labs): lab[w]=x
  if t==2:
    # swap fix: under v_Z (label Z) and v_N (label N): exchange their Z+d labels (d=R-1 at v_Z, d'=R at v_N)
    vZ,vN=rows[1][0],rows[1][1]; cz=children(rows,t,1,0); cn=children(rows,t,1,1)
    assert lab[vZ]==Z and lab[vN]==N
    # each has [Z-d,Z+d]; swap second entries
    lab[cz[1]],lab[cn[1]]=lab[cn[1]],lab[cz[1]]
  # leaves: row n-1 vertex with label e=Z-(a-sigma(a))... e = c - (Msum + a - sigma(a)) => a-sigma(a) = Z - e
  disp_to_a={a-sigma[a]:a for a in range(1,q+1)}
  for j,u in enumerate(rows[n-1]):
    e=lab[u]; a=disp_to_a[Z-e]
    for w,x in zip(children(rows,t,n-1,j),tuples[a]): lab[w]=x
  return rows,par,lab
