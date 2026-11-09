from check import *
def main():
 x=S.symbols('x1:4');y=S.symbols('y1:4');p=(4,4,2);a=(0,3,2);pp=(9,8,4);aa=(1,6,4)
 lhs=expand(*literal(aa,pp),3)
 rhs={tuple(2*v+(i==0) for i,v in enumerate(b)):c%2 for b,c in expand(*literal(a,p),3).items() if c%2}
 diff={b:1 for b in set(lhs)|set(rhs) if (lhs.get(b,0)+rhs.get(b,0))%2}
 assert len(diff)==32
 expr=sum(S.prod(x[j]**b[j]*y[j]**(pp[j]-b[j]) for j in range(3)) for b in diff)
 D12=x[0]*y[1]+x[1]*y[0];D13=x[0]*y[2]+x[2]*y[0];D23=x[1]*y[2]+x[2]*y[1]
 target=x[2]*D12**7*D13**2*D23
 assert S.Poly(expr-target,*x,*y,modulus=2).is_zero
 assert max((11,10))+max(pp)<21
 out={'status':'PASS','coefficient_field':'F2','f':'x2^3*x3^2*y1^4*y2','residual':'x1','result':'T(x1*f^2)+x1*T(f)^2 = x3*D12^7*D13^2*D23 != 0','Dij':'xi*yj+xj*yi','input_row_one':aa,'input_row_two':[pp[j]-aa[j] for j in range(3)],'margins':[[11,10],pp],'strict_interior':True,'difference_row_one_exponents':sorted(diff),'terms':32}
 (P/'interior-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='difference_row_one_exponents'},indent=2))
if __name__=='__main__':main()
