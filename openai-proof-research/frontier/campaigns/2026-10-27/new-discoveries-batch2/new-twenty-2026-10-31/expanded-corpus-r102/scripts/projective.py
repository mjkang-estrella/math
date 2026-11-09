import json
for name,period,order in [('tetrahedral',6,12),('octahedral',12,24),('icosahedral',30,60)]:
 def numerator(p):
  if name=='tetrahedral':return 2*p+1+8*[1,0,-1][p%3]+3*(-1)**p
  if name=='octahedral':return 2*p+1+8*[1,0,-1][p%3]+9*(-1)**p+6*[1,1,-1,-1][p%4]
  return 2*p+1+20*[1,0,-1][p%3]+15*(-1)**p+12*[2,1,0,-1,-2][p%5]
 vals=[numerator(p)//order for p in range(10001)]
 assert all(numerator(p)%order==0 for p in range(10001))
 assert all(vals[p+period]==vals[p]+1 for p in range(10001-period))
 print(json.dumps({'canonical_group':name,'rotation_group_order':order,'through_p':10000,'zeros_excluding_zero':[p for p,x in enumerate(vals) if p and x==0],'period':period,'dimension_increase_over_period':1,'initial_period':vals[:period]}))
