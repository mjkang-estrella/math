import sys,json
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 # Connected threshold graphs: first isolated, last dominating; interior bits arbitrary.
 bounds={}
 for k in range(1,n-1):
  for a in range(n-k-1):
   m=n*k-k*(k+1)//2+a
   bounds[m]=k*(n-1)**3+a*(k+1)**3+(n-k-a-1)*k**3+(k+a)**3
 limit=(n-1)*(n-2)//4
 count=0;best={};viol=[]
 for bits in range(1<<(n-2)):
  q=bits;suffix=1;m=n-1;F=(n-1)**3
  for i in range(n-2,0,-1):
   b=(q>>(i-1))&1;m+=i*b;F+=(suffix+i*b)**3;suffix+=b
  F+=suffix**3
  if m>limit:continue
  count+=1
  if m not in best or F>best[m][0]:best[m]=(F,bits)
  if F>bounds[m]:viol.append([m,F,bounds[m],bits])
 print(json.dumps({'n':n,'source_m_upper_bound':limit,'connected_threshold_sequences_in_scope':count,'violations':viol[:10],'max_excess':max((v[0]-bounds[m] for m,v in best.items()),default=0)}),flush=True)
 if viol:break
