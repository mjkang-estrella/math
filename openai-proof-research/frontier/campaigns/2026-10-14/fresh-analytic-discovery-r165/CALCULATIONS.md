# Intrinsic metrics: prefreeze calculations

PREFREEZE. No theorem is frozen and no author-proof nominee is offered. Codex / GPT-6 Astra / high / default service tier. Only SOURCE325 is developed. These calculations start after complete reading of both pinned proof paths and their includes, actual primary DD/BCD/LS/HM operations, ACV sections 4 and 8, and original R016/R019/R024 and matrix-disk/crouzeix-five mathematical sections. Paulsen's original paper remains inaccessible; no result below is presented as a new proof of his theorem. Protected identities, versions and excerpts are private.

## 1. A first distinction that cannot be skipped

Let B be a unital C*-algebra, a in B, K its state numerical range, and Omega an admissible analytic convex domain with K compactly contained in Omega. Write t=f(a) for an interior disk coordinate. For a faithful representation pi:B->B(H), SOURCE325 supplies complete norm bounds and, by the finite-compression construction below, a positive metric h_ext in B(H). The question examined here is whether a metric with condition number at most two can be chosen in B itself, uniformly over all B,a at this full scope. This is a prospective question, NOT a frozen theorem or an assertion of literature novelty.

The three locations B, pi(B)'', and B(H) must remain distinct. A bounded weak-operator subnet of external metrics stays in B(H); it does not land in pi(B)'' without an additional argument. Likewise a weak* limit in B** is not an element of B. Ordinary complete amplification does not state an internal similarity theorem.

## 2. The entire external infinite-dimensional construction is paid

Choose an analytic convex Omega_1 with K subset Omega_1 and closure Omega_1 subset Omega. Put q=max_closure(Omega_1)|f|<1. Direct finite compressions of a (with a fixed scalar z0 in Omega_1 on their complements) have numerical ranges in Omega_1. The structural source provides h_E on the finite part, 1<=h_E<=4, making g(a_E) contractive for the disk coordinate g of Omega_1. Its common positive representation then gives

 t_E* h_E t_E <= q^2 h_E,    t_E=f(a_E).

Extend h_E by the identity on the complement. As E ranges over all finite-dimensional subspaces, a_E and a_E* converge strongly to pi(a) and pi(a)*. A fixed contour inside Omega_1 outside K union {z0}, with positive numerical-range distance, gives uniform resolvent bounds. Resolvent identities and contour integration give strong-* convergence t_E->pi(t). A weak-operator cluster point therefore gives

 1<=h_ext<=4,    pi(t)* h_ext pi(t)<=q^2 h_ext.

No separability is needed: use the directed net, not a sequence. For the mixed product limit, t_E x converges in norm and the h_E are uniformly bounded; hence the quadratic forms pass to the limit. Every matrix coefficient size and analytic test then uses the same h_ext. This is a standard compactness/compression extension of the actual source, not a substantial candidate.

## 3. Strictness buys simultaneous endpoint slack externally

Set d=1-q^2>0 and M=||t||. Choose 0<eta<min(1/4,d/[4(1+M^2)]), and define

 k=(1-eta)h_ext+(5eta/2)I.

Then

 (1+3eta/2)I <= k <= (4-3eta/2)I,
 k-t*k t >= ((1-eta)d-(5eta/2)max(M^2-1,0)) I >= d/8 I.

The final d/8 is deliberately conservative: eta<=1/4 gives (1-eta)d>=3d/4, while eta<=d/[4(1+M^2)] makes the subtraction <=5d/8. Thus strict enclosing geometry pays a metric strictly inside all three inequalities. No boundary-attainment theorem is needed for this step.

## 4. A completely explicit internal metric at a weaker cost

The internal Stein series

 h0=sum_(j>=0) t*^j t^j

converges in norm since r(t)<1, belongs to B, and h0-t*h0 t=1. SOURCE325 applied to the rectangular polynomial/holomorphic column (1,f,...,f^N), embedded in a square matrix, gives

 h0 <= [4/(1-r^2)]1,   r=max_K |f|<1.

A better constant retaining the exact constant term is obtained from each tail column:

 h0 <= [1+4r^2/(1-r^2)]1.

Thus h0^(1/2) is an internal similarity to a contraction, but its condition bound sqrt((1+3r^2)/(1-r^2)) exceeds two for r^2>3/7. This is fully paid functional calculus plus a geometric series; it does NOT solve the sharp internal question. The series varies norm-continuously wherever the spectrum stays uniformly inside the disk (locally choose a fixed resolvent contour).

## 5. Conditional expectation supplies one missing bridge

In the universal representation pi_u, if a unital positive B-bimodule map E:B(H_u)->pi_u(B)''=B** is available, applying E to the external strict metric k preserves its three inequalities, since E(t*k t)=t*E(k)t. This gives a metric in the universal bidual B**. An arbitrary represented bicommutant is insufficient for the subsequent weak*-to-norm argument. The availability of E is an additional hypothesis, not a consequence asserted for an arbitrary C*-algebra. Finite-dimensional represented algebras have an explicit such map by block pinching and states on multiplicity factors. The general no-expectation case remains separate.

The next notebook develops the norm-approximation and Stein-repair step completely, and then tests what the source's dual construction does without E. No internal sharp theorem is currently frozen.

## Late stronger series comparison

The complete ACV Section 3 proof was read after this initial feasibility note. It improves the ordinary Stein-series bound to min(1+4r²/(1-r²),1/(1-r)) and supplies the discounted internal metric k_r=sum_j r^(2j)t*^j t^j with k_r<=1/(1-r²) and t*k_r t<=k_r. Hence the sharp-two small-image range extends to r<=sqrt(3)/2. REDUCTIONS §5 records the exact compatibility calculation and late chronology. This supersedes the initial 3/7 threshold as the strongest paid threshold; no frozen statement changed.
