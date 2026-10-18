# Unpaid orthogonality interface and tested routes

Author: Myeongjin Kang. Original text CC BY 4.0. Exploratory screen, no frozen
candidate, no theorem of orthonormal convergence claimed.

Write s=n/[2(n+1)]. For a measurable graph τ:Ω→[0,1), define, initially on
frequency-truncated inputs,

    T_τ g(x)=S(τ(x))(1−Δ)^(−s/2)g(x).

A natural sufficient interface for an orthonormal-density maximal theorem
is a uniform Schatten bound

    ||T_τ* M_w T_τ||_{S^{β'}} ≤ C ||w||_∞,                         (A)

for all such graphs, bounded weights, and all finite frequency cutoffs, for
some β>1. Here Ω is a unit ball, M_w is multiplication, and β'=β/(β−1).
For positive weights the operator is positive; complex weights can be
split into four positive parts with an absolute constant. Schatten duality
then bounds ∫w Σλ_j|T_τg_j|² by C||w||∞||λ||ℓβ for every finite L²
orthonormal system. For nonnegative λ choose one maximizing time for the
whole density, not separate times for each particle. Absolute values of
λ dominate the signed case. Finite-rank approximation and a maximal
principle would then give a density convergence statement. These last
steps are standard and already performed in BKS §6.1; (A) is the debt.

The static necessary condition in BKS §6.3 Condition 2, specialized to
Lebesgue measure, is β≤n/(n−2s)=(n+1)/n. It does not prove that every
β below this ceiling works. No full exponent range has been frozen here,
and no conjecture is presented as a proved deduction.

## 1. Scalar L^r control has no abstract Schatten consequence

The weighted-tree calculation proves a uniform scalar T_τ:L²→L^r bound
for some r>2. That alone cannot imply (A), even with spatially localized
operator norm bounds. On the probability space [0,1], let ε_j be independent
Rademacher functions, and define T_M(c)=Σ_{j=1}^M c_j ε_j. Then T_M is an
isometry from ℓ²_M to L². For real c,

    E exp(uT_M c)=Π_j cosh(uc_j)≤exp(u²||c||²/2).

Markov's inequality at u=v/||c||² gives a Gaussian two-sided tail, and
integration r∫v^(r−1)P(|T_Mc|>v)dv gives
||T_Mc||_r≤C_r||c||₂ uniformly in M. Complex inputs follow by real/imaginary
splitting. In particular ||1_E T_M||₂→₂≤C_r |E|^(1/2−1/r), exactly a
positive local mass gain. Nevertheless T_M*T_M=I_M, whose S^ρ norm is
M^(1/ρ) for every finite ρ. The infinite map is not compact. This is an
abstract implication counterexample, not a Schrödinger counterexample.

## 2. Frequency trace interpolation loses a positive power

Let T_{τ,N} use a fixed smooth annular multiplier ψ(ξ/N)N^(−s) instead
of (1−Δ)^(−s/2), and put K_N=T_{τ,N}*T_{τ,N}. Its diagonal trace is
exactly C_ψ |Ω| N^(n−2s), because the modulus of the oscillatory factor is
one. The scalar lemma supplies ||K_N||op≤C. The elementary trace/operator
interpolation therefore gives only

    ||K_N||_{S^ρ}≤C N^((n−2s)/ρ),   1≤ρ<∞.

This upper bound grows at every finite ρ; summing it by a frequency
triangle inequality does not prove (A). It is not a lower bound on K_N,
and it does not exclude a better estimate exploiting oscillation.

## 3. Exact loss in the existing density proof

Bez–Kinoshita–Shiraki, arXiv:2306.14536v1, §6.2, equations (6.13)–(6.15),
uses a spatial dyadic shell |x−y|≈2^(−l), frequency N=2^k, and the absolute
kernel bound from Lemma 6.1. For α=n and 1<β<2 the interpolated shell
bound has factor

    2^((n−2s)k) 2^(−nl/β) (1+2^(k−l))^(−n/2).

Already its l=0 contribution scales as 2^((n/2−2s)k). At the source
critical s this exponent equals n(n−1)/[2(n+1)]>0. The proof's
frequency summation is thus unavailable. Their separate s=n/4 endpoint
argument uses a uniform full kernel of order |x−y|^(−n/2), Lemma 6.3;
it does not provide the needed kernel below n/4. The failure belongs to
this absolute-kernel estimate, not to the desired maximal theorem.

Interpolation between this known higher-regularity Schatten theorem and
the source scalar critical theorem produces higher-regularity conclusions.
It cannot retain s exactly critical with a positive Schatten improvement.
Such interpolation would also be technical, not a new candidate.

## 4. A current eigenvalue-counting method does not transfer verbatim

Hadama–Toyoshima, arXiv:2608.21823v1, Theorem 1.4, proves endpoint
orthonormal Strichartz estimates for product spacetime norms. Its
near/far method is real spectral information, unlike scalar interpolation.
But the operative local estimate, Lemma 4.4, is

    1_{E_k}1_I fUU*f1_{E_k}1_I ≤ B² 2^k |I| 1_{E_k}1_I.

The factor |I| comes from integration with respect to dt and the
fixed-time energy bound. A common graph uses dx pushed to (x,τ(x)),
which may have an atom in time. For τ≡0 and I containing 0, shrinking I
does not shrink the graph operator at all. Choose any nonzero compact-
frequency g whose (1−Δ)^(−s/2)g has nonzero norm on Ω; its graph norm
stays fixed. Therefore a uniform O(|I|) near estimate on graph measure
is false. The source descendant bound instead depends on frequency and
spatial rescaling, with a cutoff at relative depth j. Replacing the
product-measure local estimate by that frequency-dependent one and
closing the spectral band sum is a new missing argument; it has not
been obtained here. The current paper does not itself assert (A).

Only Theorem 1.4, the key-ideas opening, the full far-part proof, and the
near-part opening through Lemmas 4.4–4.5 were read. No claim of reading
the full spectral-band proof is made. The 2026 Bhimani–Choudhary
waveguide paper was checked at its stated necessary condition and its
explicit description of the rank-one reduction; that condition does not
supply an orthogonality-sensitive counterexample to (A).

## Disposition

The scalar weighted lemma is proved author-side and assessed technical.
The stronger density interface is unresolved, not refuted. No natural
full target was frozen and no restricted or higher-regularity substitute
is nominated. A further useful attempt would require actual
rank-sensitive common-time-tree control, not another assertion that
initial orthogonality or scalar boundedness automatically gives (A).
