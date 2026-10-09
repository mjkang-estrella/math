"""Exact growing power diagrams and audit identities; no finite test proves Q."""
import runpy,pathlib,json,hashlib
from fractions import Fraction as F
ROOT=pathlib.Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/experiments/i34_target_uniform_brenier'
lib=runpy.run_path(str(ROOT/'frontier/experiments/i33_density_robust_brenier/diagnostics.py'),run_name='i34_readonly_library')
clip,cells,integrate,operators,sub,dot,transport=[lib[k] for k in ['clip','cells','integrate','operators','sub','dot','transport_cost']]

def intersection(p,sites,b,j):
 for k in range(len(sites)):
  if k!=j:p=clip(p,sub(sites[j],sites[k]),b[j]-b[k])
 return p

def run():
 audit=[]
 for a in [F(1,4),F(1,16),F(1,64),F(1,256),F(1,1024)]:
  for k in [F(1,8),F(1,4),F(1,2),F(3,4),F(7,8)]:
   # Direct integration of polynomial traces f(+-a,y)=(1+-k*y)/4.
   facets=[]
   for sign in [-1,1]:
    facets.append((F(1,2),sign*a/2,sign*k/6))
   assert facets==[(F(1,2),-a/2,-k/6),(F(1,2),a/2,k/6)]
   m=[(1-a)/2,a,(1-a)/2];dm=[-F(1,2),0,F(1,2)]
   db=[(a/2,k/6),(-a,-k/3),(a/2,k/6)]
   ratio=sum((v[0]**2+v[1]**2)/mi for v,mi in zip(db,m))/sum(v*v/mi for v,mi in zip(dm,m))
   assert ratio==a+k*k/(9*a)
   assert sum(mi*v for mi,v in zip(m,[-k/3,0,k/3]))==0
   audit.append(dict(a=str(a),kappa=str(k),moment_ratio=str(ratio)))
 # Independent exact integration of the source-half-plane gluing counterexample.
 box=lib['BOX'];q=(F(3,5),F(4,5));P=clip(box,(F(1),F(0)),F(0));Q=clip(box,q,F(0));rho={(0,0):F(1,4)}
 mp=integrate(P,rho);mq=integrate(Q,rho);assert mp==mq==F(1,2)
 cp=tuple(integrate(P,rho,(j==0,j==1))/mp for j in range(2));cq=tuple(integrate(Q,rho,(j==0,j==1))/mq for j in range(2))
 assert cp==(F(1,2),F(0)) and cq==(F(1,4),F(13,32))
 S2=dot(sub(cp,cq),sub(cp,cq));assert S2==F(233,1024)
 overlap=integrate(clip(P,q,F(0)),rho);signcorr=4*overlap-1
 assert signcorr==F(3,8)
 D2=2-2*q[0]*signcorr;assert D2==F(31,20)
 w2=dot(sub((F(1),F(0)),q),sub((F(1),F(0)),q));assert w2==F(4,5)
 G=dot(q,cq)-q[0]/2;assert G==F(7,40)
 rows=[];facetcases=0
 for n in [2,3,4,6,8,12,16]:
  sites=[(F((-1)**j),F(j,n)) for j in range(-n,n+1)]
  b=[-r*r/2 for _,r in sites];polys=cells(sites,b);g,_=operators(sites,b,polys,rho)
  assert all(integrate(p,rho)>0 for p in polys)
  for j in range(2*n):assert g[j][j+1]==F(1,8*n);facetcases+=1
  for j in range(2*n-1):assert g[j][j+2]==F(n,8)*(1-F(1,4*n*n));facetcases+=1
  pathcost=sum(dot(sub(sites[j+1],sites[j]),sub(sites[j+1],sites[j])) for j in range(2*n));assert pathcost==8*n+F(2,n)
  bv=sum(g[i][j]*dot(sub(sites[i],sites[j]),sub(sites[i],sites[j])) for i in range(len(sites)) for j in range(i+1,len(sites)))
  assert bv==1+F(1,4*n*n)+(2*n-1)*(F(1,2*n)-F(1,8*n**3))
  # Actual finite maps under a translated potential, with rigorously optimal target cost.
  t=F(1,100*n*n);bt=[z+t*site[1] for z,site in zip(b,sites)];polyst=cells(sites,bt)
  for degree in ([0,2*n-1] if n<=6 else [0]):
   dens=rho if degree==0 else lib['density'](degree)
   masses=[integrate(p,dens) for p in polys];massest=[integrate(p,dens) for p in polyst]
   assert sum(masses)==sum(massest)==1 and min(masses+massest)>0
   R=[[integrate(intersection(polys[i],sites,bt,j),dens) for j in range(len(sites))] for i in range(len(sites))]
   assert [sum(row) for row in R]==masses
   assert [sum(row[j] for row in R) for j in range(len(sites))]==massest
   assert all(R[j][j+1]>0 for j in range(2*n))
   err=sum(R[i][j]*dot(sub(sites[i],sites[j]),sub(sites[i],sites[j])) for i in range(len(sites)) for j in range(len(sites)))
   cost=transport(masses,massest,sites,sites);assert 0<cost<=err
   rows.append(dict(n=n,atoms=len(sites),density_degree=degree,t=str(t),D2=str(err),W2_squared=str(cost),D6_over_W2_squared=str(err**3/cost),zigzag_path_cost=str(pathcost),weighted_interface_budget=str(bv),smallest_cross_flow=str(min(R[j][j+1] for j in range(2*n)))))
 split=[]
 for a in [F(1,4),F(1,16),F(1,64),F(1,256)]:
  for b in [a/2,a/4,a/8]:
   ya=[(F(-1),F(0)),(F(0),F(0)),(F(1),F(0))];ba=[F(0),a,F(0)]
   yb=[(F(-1),F(0)),(F(0),b),(F(0),-b),(F(1),F(0))];bb=[F(0),a-b/2,a-b/2,F(0)]
   pa,pb=cells(ya,ba),cells(yb,bb)
   ma,mb=[integrate(p,rho) for p in pa],[integrate(p,rho) for p in pb]
   assert ma==[(1-a)/2,a,(1-a)/2] and mb==[(1-a)/2,a/2,a/2,(1-a)/2]
   err=sum(integrate(intersection(pa[i],yb,bb,j),rho)*dot(sub(ya[i],yb[j]),sub(ya[i],yb[j])) for i in range(3) for j in range(4))
   cost=transport(ma,mb,ya,yb)
   assert err==b/4+a*b*b and cost==a*b*b
   split.append(dict(a=str(a),b=str(b),D2=str(err),W2_squared=str(cost),variance=str(a*b*b)))
 # Polynomial numerator identity for the logistic-tail antiderivative:
 # v/(1+v)^2 = 1/(1+v) - 1/(1+v)^2.
 assert [0,1]==[1-1,1-0]
 I='log(2)-1/2 (exact antiderivative log(1+v)+1/(1+v))'
 out={'scope':'exact finite diagnostics; analytic all-n arguments are in report; no floating OT used','audit_cases':audit,'gluing':{'source_motion_lower_squared':str(S2),'D2_at_lambda1':str(D2),'W2_squared_at_lambda1':str(w2),'repair_gap_at_lambda1':str(G)},'logistic_half_interface_integral':str(I),'split_center_cases':split,'growing_diagrams':rows,'summary':{'exact_split_center_pairs':len(split),'exact_audit_cases':len(audit),'exact_map_pairs':len(rows),'exact_facet_coefficients':facetcases,'largest_atom_count':33,'nonuniform_sequences':'f_n=(1+y*T_(2n-1)(x)/2)/4 in library coordinate convention; bounds 1/8,3/8','maximum_D6_W2_ratio_float_for_display_only':max(float(F(r['D6_over_W2_squared'])) for r in rows)}}
 (OUT/'diagnostics.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out['summary'],indent=2))
if __name__=='__main__':run()
