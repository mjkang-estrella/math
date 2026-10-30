# Ordinary proof in the actual Lean convention

Research candidate; preparation only, credit 0. Theorem: for every integer r≥1,
all coefficients of the literal finite source polynomial κ_r become rationals
with odd reduced denominator after multiplication by 2^E, where
E=2r+ν₂((r−1)!). Its nonzero pure-u^r coefficient has valuation −E.
This is one shifted-parameter family, not the known original-variable law.
The complete types are in FORMAL-MAP.md and the actual audit reports.

## Literal source and formal bridge

Set P_l(z)=∏_{j<l}(z−j(j+1)) and
C_s(ξ,η)=Σ_{l=0}^s P_l(u)P_{s−l}(v)ξ^lη^{s−l}/(l!(s−l)!).
Let e_s(Z)=∏_{j=1}^s(Z−j)⁻¹, F=Σ_s C_s e_s, and L_n=[Z⁻ⁿ]log F.
At ξ=(1+i)/2, η=(1−i)/2 the literal definition is
κ_r=2^{−(2r−1)} Im L_{2r−1}. Every coefficient is finite: e_s starts at
order s, and log at order n uses only powers 1 through n of F−1.
SourceDefs encodes these geometric products and finite convolutions directly.
The Hankel formula is the source's formula, since a_l(α)=P_l(u)/(2^l l!).
No Stirling identification or analytic phase premise is required.

For the bridge put ξ=(1+it)/2, η=(1−i/t)/2 and D=−(1+t²)d/dt.
Write Δ=ξ(ξ−1)∂ξ+η(η−1)∂η, Q=ξ²∂ξ+η²∂η, Θξ=ξ∂ξ.
The product recursion for P_l gives
∂ξ C_{s+1}=(u−Θξ(Θξ+1))C_s and the analogous η identity.
Expanding operators gives
ΔQ=ξ(ξ−1)Θξ(Θξ+1)+η(η−1)Θη(Θη+1)
+ξη(2ξη−ξ−η)∂ξ∂η. The last term vanishes on the curve.
Homogeneity gives QC_s=(Δ+s)C_s and D=2iΔ there. Thus
D²C_s+2isDC_s+2iDC_{s+1}−VC_s=0,
where V=u(1+t²)+v(1+t⁻²). The identity Ze_s=e_{s−1}+se_s,
including DC_0=0, yields D²F+2iZDF−VF=0 coefficientwise.
These identities are proved in LiteralDifferential/Hankel/InverseFactor.

Work in R=Z[x,w]/(w²−1−x²). Monic division in w gives the unique integral
normal form A(x)+wB(x), so it is torsion free. Over Q, t=w+x and t⁻¹=w−x
give the Laurent algebra isomorphism, inverse to x=(t−t⁻¹)/2,
w=(t+t⁻¹)/2. Define δx=−(1+x²), δw=−wx; it respects the relation and
D=2δ. For independent integral parameters a,b set P=aw²+bwx,
h_0=0, h_1=P, and h_{n+1}=−δh_n−Σ_{1≤i<n}h_i h_{n−i}.

**Actual Lean substitution:** a=(u+v)/2, b=(u−v)/2. Denote its image H_n.
Then H_1=V/4. The source ODE divided by four is
δ²F+iZδF−H_1F=0. The finite logarithmic chain rule gives
F δlog F=δF. Differentiate and cancel F, whose constant term is 1;
coefficient comparison proves δL_n=(−i)^n H_n by induction in n.
FiniteLogChain and LogRiccatiIdentification prove this internally.
This convention differs from the historical r4 integral substitution a=u+v,
b=u−v. Here a monomial of degree d pays 2^d; it is not integral transport.

## Filtration, parity, and primitive arithmetic

Let σ be binary digit sum and q(i,j)=σ(i)+σ(j)−1 for i+j>0.
Binary subadditivity and doubling give q(e+f)≤q(e)+q(f)+1 and
q(2e)=q(e). Consider polynomials with zero parameter constant term and
coefficient e divisible in R by 2^{q(e)}. This additive class is preserved
by δ and by 2fg. It is preserved by squares: distinct parameter monomials
in a square pair to give 2f_e f_f, while diagonal terms have divisibility
2^{2q(e)}, at least 2^{q(2e)}. Independently, pair the distinct spectral
indices in the Riccati convolution; each pair is 2h_i h_j and a fixed
index contributes a square. Strong induction therefore proves every h_n
belongs to the class. Arbitrary fg is not allowed: ab is a counterexample.

ρ(x,w)=(x,−w) commutes with δ and replaces b by −b in P. Hence the
coefficient of a^i b^j has w parity j. τ(x,w)=(−x,−w) anticommutes with δ,
and τh_n=(−1)^{n+1}h_n. Every h_n belongs coefficientwise to (w), because
P does, δ(wf)=w(−xf+δf), and the recurrence preserves the ideal.
Multiplication by w sends a normal pair (C,D) to ((1+x²)D,C).
Thus ideal membership is exactly divisibility of the real normal coordinate
by 1+x², integrally. At odd n the coefficient normal form is consequently
(1+x²)A(x²)+wxB(x²), A,B integral. If j is even B=0. If j is odd and
d=i+j, q(i,j)=σ(i)+σ(j−1)≥σ(d−1), so B is coefficientwise divisible by
2^{σ(d−1)}. The extraction of the odd coordinate preserves divisibility.

The real summand has δ-primitive −Σ_k A_k x^{2k+1}/(2k+1), which is τ-odd
and vanishes at x=0. For the other summand,
δ(wf(x²))=−wx(Tf)(x²), T f=f+2(1+X)f'. On degree ≤N its diagonal is
2k+1. Solve Tf=−B downward by f_{N+1}=0 and
f_k=(−B_k−2(k+1)f_{k+1})/(2k+1). All divisors are odd units in Z_(2).
Thus f_k/2^{σ(d−1)} lies in Z_(2), and the τ-odd primitive's midpoint
x=0,w=1 lies in 2^{σ(d−1)}Z_(2). If j is even that midpoint is zero.

For uniqueness, δ(A+wB)=−(1+x²)A'+w(−xB−(1+x²)B'). A zero derivative
forces A constant; a nonzero B of degree N has a nonzero leading term
−(N+1)b_N in the second coordinate, impossible. Thus the kernel is scalar
constants. A τ-odd constant is zero. On the actual source τ conjugates the
Gaussian coordinates, so Im L_n is τ-odd. For n=2r−1,
δ Im L_n=(−1)^r H_n. The transported primitives have precisely this same
derivative and normalization, and hence equal the literal source coefficient.
Classical choice in coefficientPrimitive chooses only from proved existence
and uniqueness; it supplies no additional mathematical premise.

The substitution numerator of e=(i,j) is the integer polynomial
(u+v)^i(u−v)^j. For any target monomial m its coefficient z is an integer.
The source coefficient is a finite sum of (−1)^r z 2^{−n−d} M_e, where
M_e is the primitive midpoint above. Zero parameter support is excluded by
the weighted class. Induction in the recurrence gives total degree ≤(n+1)/2
rounded down; the odd/odd, even/even and mixed index cases give the bound
separately. Thus 1≤d≤r. Legendre gives
ν₂((d−1)!)+σ(d−1)=d−1. Factorial divisibility makes
k=ν₂((r−1)!)−ν₂((d−1)!) nonnegative. Exactly
E+σ(d−1)=n+d+k. Multiplying a summand by 2^E leaves
(−1)^r z 2^k (M_e/2^{σ(d−1)}) in Z_(2). Closure under finite sums proves
the upper bound for every m, including absent monomials and zero coefficients.

## Sharpness and attribution

Only odd/odd spectral products reach degree r at index 2r−1. Their recursion
is the Catalan recursion, so the top is (−1)^{r−1}Cat_{r−1}P^r.
The u part of H_1 is (1+t²)/4. The odd D-primitive of (1+t²)^r is
−Σ_{j<r} binom(r−1,j)t^{2j+1}/(2j+1). Using δ=D/2, the source factor
2^{−(2r−1)}, and normalized uniqueness proves
[u^r]κ_r=Cat_{r−1} I_r/2^{4r−2}, I_r=Σ_{j<r}binom(r−1,j)/(2j+1)>0.

Area's primary Theorem 1.4 already proves ν₂(I_r)=r−1+ν₂(r); it is credited,
not a new theorem. The three binomial modules prove it internally, rather
than adding it as an axiom. For its ordinary proof let c_k=k!/(2k+1)!! in Q₂.
The norms tend to zero and all moments M_i=Σ_k c_k binom(k,i) converge with
norm ≤1. The coefficient recurrence telescopes to
(i+2)M_{i+2}=(i+1)M_i. Its boundary binomial vanishes. Hence
∏_{t<j}(2t+1)M_0=2^j j!M_{2j} and M_0=0 by the norm bound.
Tails R_j=Σ_{k≥j}c_k satisfy R_0=0,R_1=−1,R_2=−4/3,
ν₂(R_j)≥ν₂(j!), so R_j/j is even for j≥2. The finite beta/binomial
transform and summation by parts give
I_{m+1}/2^m=(m+1)Σ_{j=1}^{m+1}(−1)^j binom(m,j−1)R_j/j.
The final sum is 1 plus an even 2-adic integer, proving the valuation.
Kummer and (m+1)Cat_m=binom(2m,m) give
ν₂(Cat_m)=σ(m)−ν₂(m+1). Adding the nonzero factors' valuations yields
ν₂([u^r]κ_r)=σ(r−1)+r−1−(4r−2)=−E. Multiplication by 2^{E−1}
has valuation −1 and thus even reduced denominator. At r=1, κ_1=(u−v)/4.

## Scope

The primary is *Dyadic denominator bounds and a transfer principle for the
phase constants of Jacobi zeros*, arXiv:2608.23006v2, 2026-10-05, Definition
2.1, equations (6)–(7), Theorem 1.4, Remark 3.8. The companion is
*The ultraspherical background of the Jacobi phase expansion, in closed form*,
arXiv:2609.29531v2, 2026-10-14. Cached bodies are under primary/. These are
public preprints; no journal/DOI is invented. Definitions are adopted from the
source; the differential, primitive, top and valuation ingredients are proved
internally. Mathlib's classical algebra, power-series, p-adic, Legendre,
Kummer and Catalan results remain dependencies, not claimed contributions.
The formal definition is not an all-order analytic phase identification.
Historical status prose under provenance/ is superseded by the frozen endpoint.
Final independent review/current novelty adjudication remain pending. No tests
or bounded computation serve as proof. The research proposal is one family,
credit 0; counts 2/30 additional, 32/60 total remain unchanged.
