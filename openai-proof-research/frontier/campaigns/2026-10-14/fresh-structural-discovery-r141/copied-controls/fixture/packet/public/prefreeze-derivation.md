# PREFREEZE: distinct retained coordinates of common bases

No target was frozen and no full author-proof nominee is submitted. These are feasibility calculations and a strongest-compatible-composition comparison, not an independent correctness or contribution disposition. The exact original I13 matroid question and its binary-capacity extension remain unchanged in their original file. This round does not assign them a grade. The pinned statements and operative proof operations are stipulated true.

## Question investigated

For normalized, nondecreasing, integral submodular ranks r₁,r₂ on a finite explicitly listed E, with equal total R in binary and exact rank-value oracles, let Ω be their common integer bases. For a specified A⊆E, count the distinct vectors x|A with x∈Ω, once each, with relative error ε and failure probability δ, uniformly in polynomial oracle and bit complexity in |E|, the binary input length, ε⁻¹, and log δ⁻¹, including exact zero detection. For matroids, I13 asks the same question for masks B∩A in the independence-oracle model. Neither question is weakened to bounded rank, bounded fibres, fixed dimension, or unary capacities.

The source counter counts full integer vectors, not their labelled realizations. The separate-projection identity rejected by I13 remains false. The inverse-fibre second-moment and rejection calculations in I13 remain failures of those particular estimators.

## First calculation: finite support flattening

Put n=|E|, a=|A|, h=n−a, and K=M₁⊕M₂* on paired copies of E for the matroid version. On every n-subset S set f_q(S)=q^(n−r_K(S)). The source gives addition and omission signatures on this entire domain. Sum over hidden pairs at occupancy one to obtain F_q(T) on every a-subset of the 2a visible labels. Binary contraction preserves both signatures and positivity. For a visible transversal X,

    F_q(X) = m_X + e_X,  0 ≤ e_X ≤ 2^h q,
    2^h q^n ≤ F_q(T) ≤ 2^h,

where m_X is the integer number of common-base completions. The first bound uses the integer rank deficiency ≥1 at each invalid completion.

Brändén–Huh Lemma 3.24 and Proposition 3.25 already supply coefficient powers 0<s≤1. Applied to each quadratic test, with zero entries handled by the nonnegative-matrix limit, they preserve both signatures of F_q^s. An elementary check uses u=1 on the nonzero rows of a nonnegative symmetric Q with positive index ≤1, v=Qu and c=uᵀQu. Then Q≤vvᵀ/c, so after diagonal rescaling R_ij=cQ_ij/(v_i v_j), J−R is positive semidefinite. Its entries lie in [−1,1]. The power series 1−(1−t)^s has nonnegative coefficients, hence Schur products make J−R^{∘s} positive semidefinite. This is a derivation of the classical closure, not a new lemma being nominated.

For example choose L=ceil(16 max(h,1)/ε), H=h+L(a+ceil(log₂(16/ε))), and q=2^(−H). Feasible visible fibres have F_q^(1/L) between 1 and 2^(h/L)≤1+ε/8. The total weight of all infeasible visible fibres is ≤2^a 2^((h−H)/L)≤ε/16. Thus the sum of these weights differs from the number of feasible masks by at most 3ε/16 relatively when that number is positive. Exact feasibility handles zero. All exponents have polynomial bit descriptions.

The source's full-domain two-signature transport interface, power annealing, and capped fresh-evaluation coupling address the proposed nested evaluations: fixing a visible display leaves a positive hidden rank weight on its full valid degree; its hidden transversal sum can be counted by the same interface. Outer phases use powers ≤1/L, and the log range is bounded by nH. This route avoids inverse-fibre sampling. No nested counter implementation or full bit-complexity proof was drafted: the exact representation below superseded it before a target freeze.

## Stronger calculation: an exact binary-capacity representation

The following short calculation removes the multiplicities before calling any counter. Assume first Ω≠∅, R>0 and A≠∅; exact feasibility, R=0 and A=∅ are separate deterministic branches. Write D=E\A, V=E_L⊔E_R, W=A_L⊔A_R, and J=D_L⊔D_R. Let u_e=R, U=|E|R and U_D=|D|R. Define the reflected rank on E by

    r₂ᵘ(S) = u(S) − R + r₂(E\S).

It is normalized and submodular. It is nondecreasing because every marginal of r₂ is at most R. The source's reflection and translation identities give B(r₂ᵘ)=u−B(r₂). On V form the direct-sum rank k=r₁⊕r₂ᵘ. On the same ground set put

    p(S) = Σ_{e∈D} R · 1{S intersects {e_L,e_R}},
    f = k+p,     c_j=R for j∈J.

Thus B(p) has zero visible coordinates and each hidden pair has nonnegative coordinates summing to R. The source base-sum identity gives B(f)=B(k)+B(p), with total rank U+U_D. A common original base supplies a point of B(f) whose hidden coordinates all equal c: add (R−x_e,x_e) on each hidden pair to (x,u−x).

For S⊆W define the exact oracle

    g(S) = min_{T⊆J} [ f(S∪T) − R|T| ].                 (1)

This is a restricted submodular minimization on only 2|D| elements. It uses no expansion of size R. Minimizers for two sets, followed by union/intersection and submodularity of f, show that g is submodular. Monotonicity of f gives monotonicity of g. The witness above implies f(T)≥R|T|, so g(∅)=0. It also implies g(W)≥|A|R, whereas T=J gives the reverse inequality. All values are integral and between 0 and |A|R.

Writing every subset of V as S∪T shows directly from (1) that

    B(g) = { y on W : (y,c) ∈ B(f) }.                 (2)

The total equations agree by the previous rank calculation. Let b(S)=Σ_{e∈A}R·1{S intersects {e_L,e_R}}. Then B(b) imposes y_{e_L}+y_{e_R}=R and nonnegativity on each visible pair.

For an integer y∈B(g)∩B(b), (y,c) decomposes as z+t with z∈B(k), t∈B(p). This decomposition can be chosen integral: its feasible z form B(k)∩((y,c)−B(p)), an intersection of two integral submodular base polytopes. The source's reflection/translation and two-chain integrality proof apply, even when the reflected rank is not monotone. On hidden pairs, c=z+t and t has pair total R, so z also has pair total R. On visible pairs t=0 and B(b) supplies the same balance. Consequently z=(x,u−x) for an integer x∈Ω. Conversely every x∈Ω supplies such a y. The counted y is uniquely (x|A,u|A−x|A), regardless of the number of possible hidden x.

Thus these calculations identify a bijection between the desired projected vectors and the integer common bases of g and b on 2|A| coordinates. Their common total is |A|R. Each g query takes a polynomial number of original rank calls and polynomial bit work by the already-used exact submodular-minimization interface; all intermediate values have O(log((n+1)(R+1))) bits. Composing that oracle with the pinned binary-capacity counter preserves the requested every-execution polynomial bound and the same ε,δ. The feasible empty visible set has one projection; an infeasible original instance has zero.

For matroids, an equivalent classical description is ((K∨P_D)/J), where P_D is the rank-one partition matroid on hidden pairs with visible loops. Under original feasibility, J is independent in K∨P_D, of size 2h, and the union has rank n+h. Its contraction has rank a. A visible a-set is a basis exactly when it has a hidden transversal completion to a basis of K. Intersecting with the visible partition matroid counts each mask once. The rank-value formulation above also supplies polynomial independence queries without needing to enumerate completions.

## What remains, and why there is no nomination

The initial unresolved operation was uniform support representation, rather than faster inverse-fibre estimation. Calculation (1)–(2) supplies such a representation using the source's operative base calculus, integral intersection, and exact oracle operations. The main counter then applies directly. No new intermediate mixing principle, capacity compression theorem, or quantitative exponent remains to prove for this construction. The fractional-power idea is also covered by the actual classical coefficient-power closure, not only a conjectural log-concavity bridge.

I therefore do not nominate either construction as the requested nonroutine full finding. This is an author decision to stop before freezing, not a technical grade or an independent correctness verdict. The calculation is retained for parent scrutiny; it does not rewrite I13 or claim worldwide novelty, current openness, or exhaustive coverage. The short exact reduction was developed during feasibility; no extended author proof, formal verification, review, acceptance, count change, or downstream stage was attempted.
