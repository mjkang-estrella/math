# 353438: intended-model spectral proof route, scope HOLD

Clark--Thomaz--Stephen arXiv:2201.12034v1, section 4, Conjecture 1. The object is a 3-uniform hypergraph and u is its umbral index. It is not merely the ordinary graph spectral rank. The displayed edge set repeats [c,l1,l2] when i=1, whereas the subsequent equations and drawing require t+1 distinct left pleats. This lane does not turn that inconsistency into a credited counterexample. The argument below concerns the intended construction encoded by the five eigenequations; source fidelity remains a gate.

For its positive tensor eigenvector put alpha=y(c), beta=y(r1)=y(r2), gamma=y(ri), delta=y(l1), epsilon=y(lj). The source equations give
alpha/beta=rho-t/sqrt(rho),
(alpha/beta)^2=rho^2/(rho^3-(t+1)^2).
With z=sqrt(rho), necessarily z^3>t+1 and
(z^3-t)^2(1-(t+1)^2/z^6)=1.
The left side is strictly increasing on z^3>t+1. Let z0 be the positive solution of z0^3-z0=t; it exists uniquely above 1. For t>=8, z0>54/25 since (54/25)^3-54/25<8. Set h(z)=z^4-2z^3-z^2+2z-1. Expanding h(y+54/25) gives
h = y^4+(166/25)y^3+(8771/625)y^2+(156206/15625)y+104231/390625.
It is positive for y>=0. Evaluating the increasing left side at z0 and subtracting one gives h(z0)/z0^4>0. Hence z<z0 and alpha/beta=z^2-t/z<1. The source's remaining eigenequations show alpha>gamma,delta,epsilon when beta>alpha (or compare rho^3>(t+1)^2 and delta^3=(t+1)epsilon^3 directly). Thus r1,r2 are precisely the tensor maximizers.

For the clique-shadow, the positive quotient matrix in coordinate order (c,r1,ri,l1,lj) is
Q=[[0,2,0,t+1,t+1],[1,t+1,t,0,0],[0,2,0,0,0],[t+1,0,0,0,t+1],[1,0,0,1,0]].
Let L be the positive root of L^2-(t+2)L-2t=0. Choose a=b=1, c=2/L,
d=(t+1)(L+1)/(L^2-t-1), e=(1+d)/L.
This vector is strictly positive. Coordinates 2--5 of Qv=Lv hold. Coordinate 1 has positive residual
2+(t+1)(d+e)-L = (3L+2t)/(L^2-t-1)>0,
using the quadratic relation. Pairing with the positive left Perron vector gives lambda>L. The source's equations then imply a>b because a/b=(lambda^2-lambda(t+1)-2t)/lambda>1. Also a>c, a>d and d>e as shown in Lemma 5. Thus c is the unique shadow maximizer. The top-ranked vertex sets differ, so u=1 in this intended model.

The finite probe is recorded separately. The scalar proof avoids the numerical lower bound and polynomial-root approximations in source Theorem 6. It remains an ordinary proof route, not an exact MathDB Lean solution: the hypergraph definition conflict, positive Perron tensor semantics, symmetry reduction, and literal umbral-index endpoint have not been formalized. Literature search found the original paper and an author CV describing it as under review, not a comprehensive current author catalogue. No novelty clearance is asserted. Zero credit.
