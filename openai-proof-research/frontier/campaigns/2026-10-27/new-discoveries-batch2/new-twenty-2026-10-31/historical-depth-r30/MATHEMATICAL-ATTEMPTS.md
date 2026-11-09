# Exact routes and remaining gaps

No route below is a qualified discovery or formal endpoint. Ranking after reading: 386429 (concrete finite semantics but global certificate gap); 386168 (explicit analytical construction but classical reduction and original-scope gap); 386639/386640 (precise mechanisms but genuinely missing topology). Other 36 retain their original mathematical objections in results.json. Nothing is inferred from shortness or an open label.

## 386429: probability recurrence, dominance, and optimization

Read Tapp v3 §§1–4, including Definition 4.1, Proposition 4.2 and its proof sketch, Proposition 4.4, and the G(3) example; read the introduction of §5, not the entire asymptotic proof. Read Babson–Duchin–Iseli–Tucker-Foltz §§3.2, Theorems 3.4–3.5, the complete concluding independence proof, and §3.5.1 Theorems 3.12–3.13 and the complete proof of 3.13. The underlying path-rotation theorem's long folded-state proof was NOT audited. These are actual bodies, not abstract leads. Tapp's v3 and the author-hosted Models PDF are distinct versions from the publisher bodies; publication identity is bibliographic, not a collation.

For continuous iid weights, every strict edge order is equiprobable. A fixed spanning tree T is Kruskal's output iff every chord is later than each branch on its fundamental path. Necessity: otherwise the cycle maximum is a branch and exchange improves T. Sufficiency: each rejected chord closes a path of earlier T edges, while a T edge cannot close a cycle of earlier accepted T edges. These are finite exact semantics, and tie-free exchange must be formalized before a Lean theorem could certify real random weights.

Let B be tree branches and N(S) the set of chords whose fundamental path meets S⊆B. The passing-time formula gives

    F(∅)=1,
    F(S)=(∑_{b∈S} F(S\{b}))/(|S|+|N(S)|),
    P(T)=F(B).

Proof of recurrence: split permutations of S by their last branch. Their last denominator depends only on S; preceding factors are precisely the permutations of S minus that branch. This improves factorial enumeration to O(|B|2^|B|), but 8×8 has |B|=63. Dualizing gives 49 chords and 2^49 states, still far beyond a finite resource budget. This is a standard reorganization of the published exact formulas, not a new answer.

Second route: if a relabeling of branch/chord bipartite incidence graphs embeds all incidences for T into those for T', every denominator for T is at most the corresponding denominator for T'; hence P(T)≥P(T'). To prove a maximizer by this route requires an actual dominating candidate for every tree or a terminating grid-preserving move system. Complete-graph path rotation does not supply it: it moves attachments onto absent grid edges. The proof of Theorem 3.13 explicitly assumes Kn. Missing lemma: a grid-preserving probability-improving move for every nonoptimal tree, with a well-founded potential and identified terminal trees.

Third route: average stretch determines only ∑|fundamental path|, not union-neighborhood sizes in the recurrence. Exact diagnostic over all 192 trees of the 3×3 grid gives two trees with chord stretch sum 16 and probabilities 1/192 and 467/95040. All trees, edge labels and exact rationals are retained in mst-3x3-all.json; total probability is 1. This refutes using stretch alone to compute probability, but does not refute a monotonic inequality, is not the assigned 8×8 problem, and earns no credit. No 8×8 exponential sweep was run. Missing endpoint: exact global comparison on the 8×8 grid, or genuinely new approximate optimization with source-qualified significance. Merely implementing generic stochastic local search is not such an endpoint.

## 386168: nonlinear diffusion rather than pure transport

The earlier pure radial contraction objection can be addressed analytically, but not its novelty/source-scope objection. Here is an explicit route, with all coordinate factors stated. On log-radius y=log r let

    a(t)=exp(-t), s(t)=1-exp(-t), τ=1+s,
    U(z,s)=[C τ^(-1/3) - z²/(6τ)]_+,
    f(y,t)=a^(-1) U(y/a,s(t)).

Choose C>0 by (4√6/3) C^(3/2)=1, so ∫U dz=1. Direct calculation in its positive set gives U_s=(U²)_{zz}: if U=A-Bz², A'=-2AB and B'=-6B² with B=1/(6τ), A=Cτ^(-1/3). At the free boundary U=0, (U²)_z=2UU_z=0, so extending by zero adds no distributional boundary flux. Thus

    f_t=(y f)_y + exp(-4t)(f²)_{yy}.

Indeed s'=exp(-t)=exp(-4t)a^(-3), the exact transformed time coefficient for exponent m=2. This supplies a nonlinear diffusion term, not only transport. Its principal coefficient is 2exp(-4t)f≥0; it degenerates at the moving boundary. Every compactly supported 1D porous-medium solution can be used instead of U by the same transformation with bounded s∈[0,1).

For n≥2 let σ be normalized sphere area measure and define μ_t by pushforward of f(y,t)dy dσ(θ) under x=exp(y)θ. Its Lebesgue density is ρ=f(log r,t)/(ω_{n-1}r^n), not f/r^(n-1). On the annulus write F=ω_{n-1}r^nρ and D=r∂r. The physical PDE is

    ρ_t = (ω_{n-1} r^n)^(-1) D[(log r)F + exp(-4t)D(F²)].

It is a radial nonlinear degenerate parabolic equation with zero angular diffusion. Its radial principal coefficient on ρ_rr is 2exp(-4t)r²F≥0. Since U's support stays uniformly bounded for τ∈[1,2], support in y shrinks at rate O(exp(-t)); testing bounded continuous functions proves μ_t⇀σ on the unit sphere. This is an ordinary explicit calculation, not a fully established well-posedness theorem for arbitrary initial data or an autonomous isotropic equation. The equation is time-dependent, rank-one diffusive, and coefficients were engineered by conjugation. Those qualifications may matter in the unread original workshop scope.

Two alternatives fail or remain restricted: (i) setting the diffusion coefficient to zero only reproduces the old transport objection; (ii) tangential diffusion alone with normal deterministic drift provides no nonlinear radial smoothing; adding a density-dependent radial diffusion gives the above standard porous-medium conjugation. Because the entire mechanism is a direct explicit bridge from the classical Barenblatt family under a coordinate/time change, no discovery claim is made for this engineered example. Original AIM hypotheses and any requirement of an autonomous equation/general attraction remain material gaps. No surrogate Lean formalization is warranted.

## 386639 and 386640: knots versus rational concordance classes

Read Livingston's actual published AGT 2010 paper: definition on p2191; Theorems 1–2 on p2192; §7 Theorem 5/Corollary 6, infection-family description, Theorem 7 and complete Theorem 8 proof pp2197–2199; §7.2, §8 questions and Appendix A limiting argument. Did not read/audit Gilmer's external proof, the earlier infection computations, or collate arXiv and published versions. These are missing dependencies, not certified axioms in a new endpoint.

Route 1: Theorem 8 builds K(J,-J) with (1-ε)/2≤g_st≤1/2. Its upper bound is a genus-one surface for 2K by surgery on a slice J#-J curve. This does NOT prove a strict upper bound. Making J signatures large changes only the lower estimate. Sending ε→0 also changes J; it cannot furnish a single knot below 1/2. The visible minus signs in PDF text extraction are damaged; formulas here use the published K(J,-J) setting evidenced by its slice J#-J surgery, visually confirmed on rendered published p2199 (sources/livingston-page-09.png).

Route 2: §7.2 states g_st≤m/(m+1), with a lower bound (m-1)/m for a suitable J, for K(J,-mJ). The published first displayed genus inequality on p2200 literally prints g4((m+1)K)≤m/(m+1), which is incompatible with its intended positive-genus discussion; do not use that printed genus inequality as a valid input. The stable inequality is separately stated. Only a sketch is given there, not a complete geometric proof of the multi-copy construction. The page was visually inspected (sources/livingston-page-10.png). For every positive integer m the upper bound is at least 1/2. Replacing m by a fraction is not defined as an infection knot. In C⊗Q it is trivial to divide a positive-norm element by a large integer; that is not an actual knot in C, and clearing denominators reverses the improvement. Missing geometric lemma: an actual knot with g4(qK)<q/2 and an independent positive stable lower bound. q=3 and g4(3K)=1 would suffice together with positivity; no such surgery supplied by these diagrams.

Route 3: any integer-valued concordance homomorphism h with |h|≤g4 satisfies |h(K)|≤g_st(K), by applying it to nK then dividing by n. Consequently a positive candidate below 1/2 must have every such h zero. Ordinary nonzero signature/τ/s-type lower bounds cannot certify this target. Character-dependent Casson–Gordon estimates can give fractional lower bounds, as Theorem 8 demonstrates, but must be paired with a genuinely better multi-copy surface, not a smaller error bar. No finite search over knot names supplies that surface.

For 386640, the same homomorphism estimate means all these h must vanish. Torsion gives g_st=0 but contradicts infinite order. A Casson–Gordon obstruction with a linear lower bound proves infinite order at the expense of positive stable genus. One instead needs both a nonlinear/unbounded order obstruction and sublinear upper-bound surfaces g4(nK)=o(n). Neither follows from the stable seminorm axioms. This remains a held source problem; the paper itself asks the norm-kernel question. No claim about its complete current open status is made.

Primary classical diffusion comparison: read Vázquez, *Porous medium flow with nonlocal effects*, Traditional porous medium presentation and slide 26/41, actual Barenblatt formula, α=n/(2+n(m−1)), β=1/(2+n(m−1)). This is an author lecture body, not a research-paper proof or a complete solution to the workshop question. The explicit m=2,n=1 bridge above is verified by differentiation; no nonlocal theorem is being applied. Author-hosted JEE501.pdf failed TLS certificate verification once; no retry or bypass. Distinct TU Berlin hosted lecture retrieved successfully.
