import sys,time,random
src=open(sys.path[0]+'/orderable_binary_search.py').read().split('t=time.time()')[0]
sys.argv=['x','3','7','0']; exec(src); exec(open(sys.path[0]+'/orderable_fast.py').read())
inc_=lambda E:[(1<<a)|(1<<b) for a,b in E]
A=[3,5,6,7]; F7s=[1,2,4,8]+[sum(((A[j]>>i)&1)<<j for j in range(4)) for i in range(3)]
P=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(5+i,5+(i+2)%5) for i in range(5)]
tests=[('F7',[1,2,4,3,5,6,7],False),('F7*',F7s,False),('K4',inc_([(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]),True),('K5',inc_([(a,b) for a in range(5) for b in range(a+1,5)]),True),('K33',inc_([(a,b) for a in range(3) for b in range(3,6)]),True),('R10',[v for v in range(32) if bin(v).count('1')==3],False),('Petersen',inc_(P),True)]
for nm,v,e in tests:
    c=circuits(v); print(nm,orderable_fast(len(v),c),e)
# random agreement test against the slow solver on random binary matroids of rank 5-6
random.seed(7); agree=0; tot=0; t=time.time()
while time.time()-t<60:
    r=random.choice([4,5,6]); m=random.randint(r+1,min(2**r-1,r+6))
    v=random.sample(range(1,1<<r),m)
    c=circuits(v); a=orderable(m,c); b=orderable_fast(m,c); tot+=1; agree+=(a==b)
    if a!=b: print('DISAGREE',v,a,b); break
print('random agreement',agree,'/',tot)
