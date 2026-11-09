import sys,math,json,time
lo,hi,N=map(int,sys.argv[1:]);mask=(1<<48)-1
for m in range(lo,hi+1):
 b=[math.comb(m,j) for j in range(m+1)];c=[(-1)**(j+1)*b[j] for j in range(m+1)];a=[0]*(4*N+1);a[0]=1
 for n in range(1,len(a)):
  a[n]=(sum(c[j]*a[n-j] for j in range(1,min(m,n)+1))+sum(b[j]*a[(n-j)//2] for j in range(n%2,min(m,n)+1,2)))&mask
 bad=[];hist={}
 for n in range(1,N+1):
  d=(a[4*n]-a[n])&mask;v=(d&-d).bit_length()-1 if d else 48;vn=(n&-n).bit_length()-1
  k=m//2;goal=vn+(2*((k&-k).bit_length()-1)+3 if m%2==0 else 3 if m%4==1 else 6)
  hist[v-goal]=hist.get(v-goal,0)+1
  if (m%2==0 and v!=goal) or (m%2==1 and v<goal):bad.append([n,v,goal])
 print(json.dumps(dict(m=m,n_range=[1,N],modulus_bits=48,bad=bad[:20],bad_count=len(bad),excess_hist=hist)),flush=True)
