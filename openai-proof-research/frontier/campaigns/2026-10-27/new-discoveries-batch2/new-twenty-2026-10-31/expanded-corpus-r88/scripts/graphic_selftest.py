import sys; sys.argv=['x']
exec(open(sys.path[0]+'/graphic_test.py').read().split("if __name__")[0])
inc=lambda E:[(1<<a)|(1<<b) for a,b in E]
K5=inc([(a,b) for a in range(5) for b in range(a+1,5)])
K34=inc([(a,b) for a in range(3) for b in range(3,7)])
R10=[v for v in range(32) if bin(v).count('1')==3]
A=[3,5,6,7]; F7s=[1,2,4,8]+[sum(((A[j]>>i)&1)<<j for j in range(4)) for i in range(3)]
for name,v,exp in [('M(K5)',K5,True),('M(K3,4)',K34,True),('R10',R10,False),('F7',[1,2,4,3,5,6,7],False),('F7*',F7s,False)]:
    print(name,is_graphic_3conn(v)[0],'expected',exp)
