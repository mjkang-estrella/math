import pathlib,json,math,functools
D=pathlib.Path(__file__).resolve().parents[1];rows=[];hits=[]
for k in [4,5,6]:
 b=k//2;c=k-b;dp=[0]*1201;bal=[0]*1201;arg=[0]*1201
 for n in range(2,len(dp)):
  def cross(a):
   z=math.comb(a,b)*math.comb(n-a,c)
   if b!=c:z+=math.comb(a,c)*math.comb(n-a,b)
   return z
  dp[n],arg[n]=max((dp[a]+dp[n-a]+cross(a),a) for a in range(1,n//2+1))
  a=n//2;bal[n]=bal[a]+bal[n-a]+cross(a)
  if dp[n]>bal[n]:hits.append({'k':k,'n':n,'opt':dp[n],'even':bal[n],'split':arg[n]})
 rows.append({'k':k,'max_n':1200,'optimal_counts':dp,'argmax_splits':arg,'even_counts':bal})
 print('done',k,'hits',len(hits),flush=True)
(D/'outputs/even-dp.json').write_text(json.dumps({'rows':rows,'hits':hits},indent=2))
