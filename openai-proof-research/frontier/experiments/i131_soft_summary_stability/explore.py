"""Finite floating-point exploration, not a universal certificate."""
import json,math

def psi(x):
    return sum(t*math.log(t) if t>0 else 0 for t in [(1+x)/2,(1-x)/2])+math.log(2)
def mean(v):return sum(v)/len(v)
def information(u):return mean([psi(x) for x in u])-psi(mean(u))
def noise(u,rho):
    v=u[:]
    for i in range((len(u)-1).bit_length()):v=[(1+rho)/2*v[j]+(1-rho)/2*v[j^(1<<i)] for j in range(len(v))]
    return v
def solve(fun,target,lo,hi):
    if fun(hi)<target-1e-13:return None
    for _ in range(70):
        mid=(lo+hi)/2
        if fun(mid)<target:lo=mid
        else:hi=mid
    return (lo+hi)/2
def cube(n):return [[1-2*((x>>i)&1) for i in range(n)] for x in range(2**n)]
def run():
    rows=[]
    def add(family,u,a,rho,parameter):
        n=(len(u)-1).bit_length();xx=cube(n)
        deficit=psi(rho*a)-information(noise(u,rho))
        distance=mean([x*x for x in u])+a*a-2*a*max(abs(mean([u[j]*xx[j][i] for j in range(len(u))])) for i in range(n))
        rows.append(dict(family=family,n=n,a=a,rho=rho,parameter=parameter,information_error=information(u)-psi(a),deficit=deficit,distance=distance,ratio=distance/deficit if deficit>1e-13 else None))
    for a in [.25,.5,.75]:
      target=psi(a)
      for rho in [.3,.6,.85]:
        for m in [.01,.05,.15,.3]:
          b=solve(lambda b:information([m+b,m-b]),target,0,1-m)
          if b is not None:add('biased_one_coordinate',[m+b,m-b],a,rho,{'mean':m,'amplitude':b})
        for n in [2,3,5,7,9]:
          z=[sum(x)/math.sqrt(n) for x in cube(n)]
          clip=lambda t:[min(1,max(-1,t*x)) for x in z]
          scale=solve(lambda t:information(clip(t)),target,0,30)
          if scale is not None:add('clipped_normalized_sum',clip(scale),a,rho,{'scale':scale})
          linear=solve(lambda t:information([t*x for x in z]),target,0,1/math.sqrt(n))
          if linear is not None:add('several_linear_coordinates',[linear*x for x in z],a,rho,{'scale':linear})
        for k in [2,4,6,8]:
          xx=cube(k+1);event=[int(all(t==1 for t in x[1:])) for x in xx];b0=(1-a)/2
          family=lambda b:[x[0]*(b+b0*event[j]) for j,x in enumerate(xx)]
          base=solve(lambda b:information(family(b)),target,0,a)
          if base is not None:add('exact_corrected_rare_spike',family(base),a,rho,{'epsilon':2**(-k),'correction':base-a})
        for n in [4,6,8]:
          xx=cube(n)
          def overlapping_tree(x):
            value=x[-1]
            for j in range(n-2,-1,-1):
              if x[j+1]==1:value=x[j]
            return value
          f=[overlapping_tree(x) for x in xx]
          amplitude=solve(lambda t:information([t*x for x in f]),target,0,1)
          if amplitude is not None:add('hierarchical_payload_reuse',[amplitude*x for x in f],a,rho,{'amplitude':amplitude,'boolean_mean':mean(f)})
        for k in [1,2,3]:
          r=2**k;xx=cube(k+r);u=[a*x[k+(j&(r-1))] for j,x in enumerate(xx)]
          add('independent_hierarchical_switching',u,a,rho,{'leaves':r})
    return {'scope':'floating-point exploration only; bisection information correction is approximate numerically and defined exactly by a monotone scalar root analytically','instances':len(rows),'maximum_information_error':max(abs(r['information_error']) for r in rows),'minimum_deficit':min(r['deficit'] for r in rows),'maximum_distance_deficit_ratio':max(r['ratio'] for r in rows if r['ratio'] is not None),'rows':rows}
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
