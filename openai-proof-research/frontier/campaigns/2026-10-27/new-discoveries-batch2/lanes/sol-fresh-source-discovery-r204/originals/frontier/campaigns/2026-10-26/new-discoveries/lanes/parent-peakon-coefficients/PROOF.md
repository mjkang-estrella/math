# Proposed full coefficient formula for the generalized peakon transfer matrices

Status: complete mathematical proposal, credit0; accepted25/30 unchanged.
No Lean endpoint, independent review, final manuscript or packet. Novelty and
substantive eligibility NOT decided. Standard determinant/trace identities
are credited classical tools; the source-specific determinant collapse is the
proposed bridge. Do not count individual coefficients or helpers separately.

## Literal source and proposed endpoint

Avan–Frappat–Ragoucy, arXiv2512.11066v3 (29June2026), *Quadratic Poisson
brackets for the Camassa–Holm peakons*, J.Phys.A59(2026)245202,
DOI10.1088/1751-8121/ae7683. The actual current PDF was downloaded and its
Eq2.1–2.3,4.8,5.1, Proposition5.1/Eq5.17–5.18 and Conjecture5.2/Eq5.20–5.21
read. Actual published J.Phys.A body now retrieved200; printedpp12–13 with Eq5.17–5.21 were read in text and visually inspected. The conjecture survives unchanged. Live MathDB372008 is open, all activity
arrays empty. That status is not novelty evidence. Companion grouping in the
record is not assumed accurate without reading its actual documents.

For a partition k1>=...>=kj>=1 of m, let r_s be the multiplicity of the part s.
The proposed universal coefficient is

    a_j(k1,...,kj) = m (j-1)! / ((product_i k_i)(product_s r_s!)).

This gives a1(m)=1, a_m(1,...,1)=1, and for0<=j<m-1 gives

    a_(j+1)(m-j,1,...,1)=m/(m-j),

exactly both asserted coefficient families, together with every unspecified
coefficient in the same expansion. This is a universal valid expansion; no
claim of algebraic independence/uniqueness for fixed finite N is needed.

## General algebraic determinant lemma

Work over any field K of characteristic0, with a strictly upper triangular
N×N matrix B and vectors u,v satisfying

    B-B^T = u v^T - v u^T.

Set A=(uv^T-vu^T)/2, T=(uv^T+vu^T)/2, S=B-A. For parameters λ,ξ,γ with
ξ²=λ²+γλ+1 set L=S+λT+ξA. Then, as a polynomial identity in t,

    det(I-tL) = 1-λ H(t),
    H(t)=t trace((T+γA/2)(I-tB)^(-1))
        =sum_(k=1)^N trace((T+γA/2)B^(k-1)) t^k.

The inverse is the finite polynomial I+tB+...+t^(N-1)B^(N-1), because B^N=0.
No nonsingularity premise on the numerical matrix L or spectral parameters.

### Proof of the determinant lemma

Write R=(I-tB)^(-1), a=(λ+ξ-1)/2, b=(λ-ξ+1)/2. Then
L=B+a uv^T+b vu^T. Put

    P=v^T R u, Q=u^T R v,
    C=PQ-(v^T R v)(u^T R u).

The rank-two matrix determinant lemma, with det(I-tB)=1, gives

    det(I-tL)=1-t(aP+bQ)+t²ab C.

The resolvent skew identity is

    R-R^T = t R(B-B^T)R^T,

hence sandwiching by v^T and u yields P-Q=tC. Since a+b=λ and
ab=(ξ-1)/2-γλ/4, all ξ-1 terms cancel, leaving

    det(I-tL)=1-λ[t(P+Q)/2+γt²C/4]
             =1-λ t trace((T+γA/2)R).

Every identity is algebraic over K(t); both sides are actually polynomials.
This is the load-bearing new source-specific reduction, not an assumption.

## Exact bridge to the literal source matrices

Relabel the particle positions so q1>=...>=qN. Let

    u_i=sqrt(p_i) exp(ν q_i/2),
    v_i=sqrt(p_i) exp(-ν q_i/2).

Using the exponential definitions of sinh/cosh, source Eq2.1–2.3 gives
T=(uv^T+vu^T)/2, A=(uv^T-vu^T)/2, and B=S+A is strictly upper triangular,
with B_ij=u_i v_j-v_i u_j for i<j. If positions tie, this entry is0, so ties
cause no issue in this purely algebraic statement. Relabeling is conjugation
by a permutation and preserves trace, determinant and every defined h^(k).
The source spectral functions satisfy ξ²=Λ²+γΛ+1 (Eq5.18), so λ=Λ applies.
The exact rational formulas in Eq4.8 are

    Λ=(z²-1)/(2z+γ), ξ=(z²+γz+1)/(2z+γ),

on their stated denominator domain. They satisfy the quadratic identity
identically. No Poisson bracket or flow theorem is required.

The source's Hamiltonians are literally

    h^(k)=k trace((T+γA/2)B^(k-1))  [Eq5.17].

Consequently H(t)=sum h^(k)t^k/k, and h^(k)=0 for k>N. All particles and
all trace orders are covered, rather than a finite check or arbitrary abstract
model without its source instantiation.

## All-order coefficient extraction

The classical formal trace-log identity, valid for a finite matrix over a
characteristic0 field, is

    -log det(I-tL)=sum_(m>=1) trace(L^m)t^m/m.

Using the proved determinant collapse and H(0)=0,

    sum τ_m t^m/m = -log(1-ΛH(t))
                  =sum_(j>=1) Λ^j H(t)^j/j.

For a fixed m only j<=m contributes. Ordered compositions k1+...+kj=m
produce products h^(k_i)/k_i. A partition with multiplicities r_s appears
j!/(product_s r_s!) times. Multiplying by m/j proves the displayed formula.
The source's two special coefficient families follow at once, with its
separate all-ones case explaining the upper restriction j<m-1 in Eq5.21.

## Independent exact evidence (not the proof)

check_peakon_coefficients.py builds actual matrices from arbitrary rational
u,v, imposes the literal rational spectral curve, and independently compares
both determinant and trace powers with coefficient convolutions. All24 exact
characteristic determinant identities and264 exact traces (N1..6,m1..11)
passed. This includes orders beyond N, where Hamiltonian nilpotence matters.
The universal argument is the algebra above, not these finite checks.

## Remaining gates and strongest risks

Read the actual2023 predecessor SciPost15,228 and Ragnisco–Bruschi1995:
if they already state det(I-tL)=1-ΛH, the coefficient answer may be an
immediate Newton/trace-log corollary and excluded under the strict standard.
The source calling it conjectural does not override such subsumption.
Need a bounded citation/author/registry screen and independent assessment.
The published J.Phys.A body comparison is now complete at the relevant definitions/conjecture; precise source domain
(particle assumptions, spectral exclusions) must be frozen for literal Lean.
Formalization must prove both the matrix collapse and actual source bridge,
not assume them in an abstract endpoint. The formal trace-log/Newton bridge
also needs a proved or pinned Mathlib theorem. No final eligibility claim.


## Published-source and formal checkpoint addendum

IOP's genuine published PDF was retrieved200 (520776bytes), after the web tool
reported inaccessible; no access-control bypass. Printedpp12–13 were rendered
and visually read. Conj5.2, Eq5.17–5.21 and the spectral curve match arXivv3.
Published-body source concern therefore closed for this candidate. Source
domain still must be stated carefully: the displayed square-root factors are
interpreted with coherent per-particle roots in the algebraic derivation. An
independent source reviewer must confirm the intended amplitude domain; do
not silently restrict an arbitrary principal-square-root interpretation.

The actual2023 predecessor sections2.3,4.1–4.3 and their trace/Poisson theorems
were read, together with1995 relevant Lax/Toda sections. No determinant-collapse
statement in the inspected bodies was found. This is not proof of no classical
subsumption. OpenAlex DOIworkW4417515821 has0 indexed citers, which is not
novelty evidence. Author/title web sweeps found no resolution; coverage bounded.

Root supporting Lean now compiles21 declarations in3 modules: RankTwo,
NilpotentCollapse, UpperFamily. The strict-upper nilpotence, determinant1,
finite geometric inverse and rank-two skew relation are PROVED; the endpoint
algebraicLax_det_collapse carries only the genuine spectral-curve hypothesis.
All21 actual types/axiom reports read, standard3 only. It remains an abstract
algebraic family, NOT the literal source conjecture certificate: actual
sinh/exp matrices and permutation bridge, Hamiltonian trace generator, all-order
trace/coefficient extraction and literal source endpoint remain unformalized.
No independent review, paper, packet or accepted credit.
