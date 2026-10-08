# H010: stronger obstruction for explicit intermediate coefficient storage

Independently checked paper derivation; no Lean theorem or numerical experiment.
This extends the literal-pair rejection in H010-cyclic-graeffe-obstruction.md to
variants that explicitly materialize the SAME early Graeffe layer, even using
output-sensitive multiplication. It does not exclude compressed or bypassed
layers. Verified improvement remains NONE.

## Motivation and fixed operation

Completed Opus prior-art review identified known output-sensitive multiplication
as a possible change to the frozen all-pairs operation. Root verified the primary
abstracts and retained their characteristic/sumset/failure caveats in
H010-graeffe-priorart-disposition.md. Before implementing a variant, root proposed
checking a two-free-coordinate face; native Sol derived it and native Astra
independently verified the algebra, with root repeating the finite identity.

Keep the same public family, fixed shifts, fresh uniform targets and first
2-power block. Put b0=min B_i>=64 and choose a=2^t largest <=b0/32. Then
b0/64<a<=b0/32. Set m=8a, h=2a=m/4, and assume p>2m=16a. From the independently
checked cumulative-norm identity,

    product_(xi in mu_a) A_r(xi*Z1,Z2,Z3,Z4,Z5)
      = J_a(Z1^a,Z2,Z3,Z4,Z5).

J_a has degrees <=16 in its first variable and <=16a=2m in the other four.
The whole-box CRT map into g_t modulo Y^(N/a)-1 is injective, since C1=B1/a>16,
C_i=B_i>16a and these C_i are coprime. This prior proof applies unchanged.

## Exact face and coefficient formula

Extracting leading coefficients in coordinates 1,4,5 of one S6 factor gives
S3(u2+Z2,u3+Z3,r)^8. Their top exponents require the top coefficients from every
norm factor; aggregate phase (product xi)^16=1. Hence

    [W1^16 Z4^(16a) Z5^(16a)] J_a
      = S3(u2+Z2,u3+Z3,r)^m.

Define the actual reversed shifted polynomial

    H(z,w;r)=z²w² S3(u2+1/z,u3+1/w,r),
    Phi_ij(r)=[z^i w^j] H(z,w;r)^m,  0<=i,j<=h.

Every term r^k z^s w^t of H satisfies k<=s+t. Equality terms are precisely

    1 - 2r(z+w) + r²(z-w)².

This follows directly from S3: the r² coefficient is the square of the coordinate
difference, the r coefficient has top reciprocal terms -2(z+w), and the constant
coefficient has constant term1. Shifts and curve coefficients contribute only
lower r-weight. Consequently deg_r Phi_ij<=i+j, and its possible leading
coefficient equals C_ij=[z^i w^j] ((1-z-w)²-4zw)^m.

For n=i+j and beta=1/2-m, the exact identity is

    C_ij = (-2m)_n (beta)_n / ((beta)_i (beta)_j i! j!),

where (x)_s denotes the rising factorial. There is NO additional sign factor.
A finite derivation: expand the m-th power using the -4zw term, extract from
(1-z-w)^(2m-2k), and use duplication of (-2m)_(2k). This gives

    C_ij = (-2m)_n/(i!j!) *
      sum_(k=0)^min(i,j) (-i)_k(-j)_k / ((beta)_k k!).

Terminating Vandermonde evaluates the sum as (beta+j)_i/(beta)_i, yielding the
formula. All divisions below are units in the admitted characteristic. For an
explicit check set D_s=product_(l=0)^(s-1)(2m-1-2l). Then

    C_ij = (-1)^n * product_(l=0)^(n-1)(2m-l) * D_n
             / (D_i D_j i! j!).

Because n<=2h=m/2, every integer factor here is positive and <=2m. With p>2m,
none vanishes modulo p. Thus Phi_ij has EXACT degree i+j and is not the zero
polynomial, for every fixed choice of shifts and curve coefficients.

## Preservation, exceptional targets and full work

Reverse index (i,j) identifies the forward J_a monomial

    (nu1,nu2,nu3,nu4,nu5)=(16,2m-i,2m-j,2m,2m).

All indices are in the whole injective CRT box. Therefore each coefficient
survives as a distinct coefficient of the actual canonical g_t; no other norm
monomial can cancel it under cyclic reduction.

The union of target abscissae annihilating any selected coefficient has size at
most sum_(i,j=0)^h(i+j)=h(h+1)². For uniform finite R, each x value has at most two
preimages, giving eps<=min(1,2h(h+1)²/(q-1))=O(B^-2). Outside this union,

    support(g_t)>=(h+1)²=(2a+1)²>b0²/1024=Omega(B²).

Any variant explicitly constructing and retaining that layer requires at least
that many coefficient/exponent records and record operations. In particular,
quasi-linear multiplication cannot remove actual output size. This is a storage
and materialization bound; it is not a general arithmetic-circuit lower bound.
The original all-pairs NEXT stage additionally visits Omega(B^4) term pairs on
these targets, but the broader collector bound below only needs materialization.

Let M=(h+1)², X paid attempted-query work, and Y in {0,1} emitted verified rows.
Assume every attempt costs >=1 and normal successful output materializes g_t.
Then Y*1_good<=X/M, so

    E Y <= E X/M + eps <= (1/M+eps) E X,
    E X >= 1/(1/M+eps) * E Y = Omega(B²) E Y.

This permits arbitrary caps and early abandonment. Uniform sampling of the full
group can include infinity as an additional exception of probability1/q; it does
not change the order. Conditional-history/predictable-stopping summation gives
Omega(B³) expected work for the proposed Theta(B)-row collector at constant
completion probability, versus the available B^(5/2) reference up to polylogs.
Rank failures only reduce useful reward; setup, construction, extraction and
verification add cost. No assumption that ALL solvers require Theta(B) rows.

## Scope and decision

This rejects the explicit-layer variant before an engine or pilot is built.
It does not exclude compressed coefficients, skipping the materialized layer,
changed transform orders, nonuniform targets, target-dependent shifts, multiple
outputs, or early useful dependencies. Such changes require concrete operations
and new full-cost analysis. The claim concerns supplied valid parameters; no
unproved prime-family construction or special-curve hardness is used to rescue it.
The square-root comparison is an available baseline, not a proof of optimality.

Reviewers: native Sol /root/h010_early_dependencies derived the stronger face,
finite formula and exception count; native Astra /root/h007_additive_relations
independently confirmed face/weight/formula/characteristic/whole-box preservation;
root repeated the derivation. This is a new round addressing a changed candidate
operation after the literal rejection, not duplicate initial ideation. T3 Opus
suggested the prior-art alternative but did not verify this obstruction.

No numerical work was run. Existing project checks passed with
`./scripts/check.sh > /tmp/ecdlp-h010-graeffe-check.log 2>&1` (exit0,363 audits).
Only Markdown changes followed; no new Lean claim or Audit entry. Preserve the
negative finding and turn to the independent adaptive-sampling/hybrid proposals.
Broader formal machinery has no candidate-specific justification at this point.
