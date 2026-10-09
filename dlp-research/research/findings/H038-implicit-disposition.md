# H038 implicit operators: identities retained, no full-work survivor

Factory Opus5.5's independent report is in H038-implicit-factory-raw.md, with its
full T3 task ID. Native Astra /root/h007_additive_relations COMPLETED separate
read-only mathematical/cost review. Root independently checked the identities
and identified the normalization and collision-accounting gaps before review.
No code, experiments, imports, new primary-source reads or Lean claims.
Verified improvement NONE; the existing square-root reference is unchanged.

## Convolution point-count operator

On the cyclic order-q subgroup, write real-valued g(i),h(i) with explicit pole
conventions and F(k)=sum_i g(i)h(i+k). For normalized Fourier transforms,

    Fhat(t)=q*ghat(-t)*hhat(t).

This exact identity is accepted. Conditional character-sum bounds
|q*ghat(t)|<=Dg*sqrt(p), |q*hhat(t)|<=Dh*sqrt(p) imply
|Fhat(t)|<=Dg*Dh*p/q. They do NOT give a lower bound on the RMS of arbitrary
two-factor F. The report's normalized linear/parity-bias exclusion therefore
does not follow in general. Primary theorem applicability, including trivial
characters and nondegeneracy, was not newly checked in this wave.

There is a valid narrower autocorrelation result: for h=g, Parseval and Cauchy
give

    RMS(F)^2 = q²*sum_t |ghat(t)|^4
             >= q*(sum_t |ghat(t)|²)^2 = q*RMS(g)^4.

If RMS(g)=Theta(1), Dg is fixed and p=Theta(q), the assumed coefficient bound
also gives RMS(F)=O(sqrt(q)). Consequently RMS-normalized correlation with one
additive character is O(1/sqrt(q)). A test with Fourier l1 norm O(log(q)), such
as parity on canonical indices of an odd-length cycle, gives O(log(q)/sqrt(q))
by the Fourier triangle inequality. For p not comparable to q retain the
explicit p/(q*sqrt(q)) dependence. These are LINEAR correlation bounds, not
classification-advantage bounds for arbitrary nonlinear transformations or
multi-query decoders. The RMS normalization need not give a bounded output.

For u=x-c,v=x-c', the double cover w²=u(P)v(P+Q) has genus3 only when its four
branch points are distinct and simple. Overlap, torsion-coordinate zeros,
square products and pole contributions require dispatch. General g,h need not
make F depend only on x(Q); the displayed even coordinate factors do give that
symmetry. Fixed-genus point-count cost was cited second-hand by the proposer,
not newly established or calibrated here. No actual decoder was supplied.

## Compact-coset resultant

For A(Y)=alpha*Y²+beta*Y+gamma and n>=1, the exact identity is

    Res_Y(Y^n-d,A(Y)) = gamma^n - d*U_n + d²*alpha^n,
    U_0=2, U_1=-beta,
    U_n=-beta*U_(n-1)-alpha*gamma*U_(n-2).

The doubling formula U_(2n)=U_n²-2*(alpha*gamma)^n also holds. One can see the
identity by the two formal roots of A, then extend polynomially to alpha=0.
Geometric extraction still dispatches infinity and exceptional curve cases.
For admitted rational A,Q, regular residual abscissae are x(Q+A),x(Q-A).
A finite root of Y^n-d is not the point at infinity. A genuine nonzero coset
requires d!=0 and nonemptiness, not merely n dividing p-1.

Direct residual generation and coset testing on s admitted points provide the
same soft-linear-in-s upper bound as this ring-resultant construction. That
does not prove all resultant implementations lose, or settle concrete constants.
Unknown coset-point logs remain missing from scalar recovery.

The report's two-level collision ledger has incorrect s,n dependence. Let N<=q
be the actual eligible POINT count and J the query count. Under its additional
uniform-endpoint birthday model, K~J*s*N/q reported endpoints and K~sqrt(N)
would imply

    J~q/(s*sqrt(N)), paid s*J~q/sqrt(N)>=sqrt(q).

This is only a corrected HEURISTIC invoice. Within-query dependence, repeated
endpoints, null relations, label distributions and useful rank must be justified
for an actual solver. It is not a proven lower bound. Abscissa counts cannot
replace N without accounting for actual curve points and signs.

## Pairing trace / Gauss periods

Frobenius invariance of Tr(zeta^k) under k -> p*k is accepted. Distinctness of
the claimed periods, an executable action on their representation, the pairing
point construction and within-orbit position recovery remain missing or unpaid.
An upper estimate O-tilde(sqrt(q*k_e)+k_e²) with a large right-hand expression
does NOT establish an algorithmic lower bound. The alternative d^(3/2) class-
search estimate likewise does not finish or exclude a two-stage solver.
The reported cost formulas are conditional, not a demonstrated gain or a
universal exclusion of implicit traces. No new trace-evaluation operation was
constructed. Existing H027 trace qualifications remain applicable.

## Wave decision

Retain exact Fourier and Lucas identities and the narrow autocorrelation screen.
Correct the collision arithmetic; reject broad normalized-bias and complexity
exclusions. The interval-product card is a restatement of an existing missing
primitive, not an implementation. No candidate currently meets the full-work
acceptance gate, so no numerical diagnostic or generic formalization is admitted.
Reopen on an explicit nonlinear decoder with paid sample/training costs, a
faster constrained witness extractor, or an implicit period operator with
complete position recovery. Missing operations are not free oracles.
