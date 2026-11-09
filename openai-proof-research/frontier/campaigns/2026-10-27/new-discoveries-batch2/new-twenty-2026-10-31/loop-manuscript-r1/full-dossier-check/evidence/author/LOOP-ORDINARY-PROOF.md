# Candidate for MathDB 380362 — not accepted

The precise target is Drápal–Vojtěchovský, arXiv:math/0701710, Conjecture 11.2 (p.17): two Moufang loops of order n with nonequivalent associator have multiplication-table distance at least 3n²/8. The fetched author manuscript also states exactly that conjecture. The journal route returned an HTTP 200 challenge page, not a mathematical PDF; no retry was made. Published-version comparison remains a qualification gap.

Let V=F₂³ and Q=V×F₂. Write x=(x₀,x₁,x₂), and define

f(x,y)=x₀x₁y₂+x₀y₁x₂+y₀x₁x₂.

All arithmetic in this paragraph is in F₂. Define (x,s)·(y,t)=(x+y,s+t) and (x,s)*(y,t)=(x+y,s+t+f(x,y)). Both have identity (0,0). For prescribed left factor (x,s) and product (z,u), the unique right factor is (x+z,u+s+f(x,x+z)). For prescribed right factor (y,t) the unique left factor is (z+y,u+t+f(z+y,y)). These formulas prove the loop property.

The exact source Moufang identity is ((ab)a)c=a(b(ac)). Substitution reduces its last-coordinate equality to

f(x,y)+f(x+y,x)+f(y,z) = f(x,z)+f(y,x+z)+f(x,x+y+z).

Expansion of the three displayed monomials proves this identity by cancellation in F₂. The first three coordinates agree by associativity of vector addition. The Lean proof also checks this literal identity on all 16³ triples, independently of the search script's equivalent middle Moufang identity.

Define D(x,y,z)=f(x,y)+f(x+y,z)+f(y,z)+f(x,y+z). The associator of * is (0,D(x,y,z)), in the source convention (ab)c=a(bc)[a,b,c]. Expanding D gives the determinant of the three binary vectors, so D(e₀,e₁,e₂)=1 while D(0,0,0)=0. The associative operation · has constant identity associator. No identity-preserving bijection can identify these two ternary associator maps. In fact constancy versus nonconstancy excludes equivalence under independent bijective coordinate changes as well. The exact source interpretation of 'equivalent associator' needs independent fidelity review; no reliance on just nonisomorphism of loops is made.

Finally f(x,y)=0 when x has weight 0 or 1. For each of the three vectors x of weight 2 it is one nonzero coordinate of y, and for x of weight 3 it is y₀+y₁+y₂. Thus for four x there are exactly four y with f(x,y)=1: 16 pairs. The two central coordinates s,t give four choices, so d(·,*)=64. As |Q|=16, 8d=512<768=3|Q|². This refutes Conjecture 11.2 on its printed unrestricted Moufang-loop scope.

This is one proposed result. It does not refute the strict-quarter isomorphism conjecture 380361: the example lies exactly at quarter distance. The small loop underlying this witness is classical; this investigation does not claim to discover a new isomorphism type. Author catalogues and closest-distance follow-ups were screened and selected bodies inspected; an exhaustive literature clearance and the published source comparison have not been completed. A catalogue listing a classical loop is distinct from an earlier statement of this precise distance refutation. Root must adjudicate novelty and significance.
