import pathlib
D=pathlib.Path(__file__).resolve().parents[1]
s=(D/'scripts/htriangle.py').read_text()
a=s.index(' filters=[');b=s.index('\n for m in',a)
s=s[:a]+''' filters=[0]
 for size in range(2,n+1):
  new=[]
  for bits in filters:
   bound=max((i for (i,j),idx in ix.items() if j<size and bits>>idx&1),default=0)
   for k in range(bound,size):new.append(bits|sum(1<<ix[i,size] for i in range(1,k+1)))
  filters=new
'''.rstrip()+s[b:]
(D/'scripts/htriangle-fast.py').write_text(s)
