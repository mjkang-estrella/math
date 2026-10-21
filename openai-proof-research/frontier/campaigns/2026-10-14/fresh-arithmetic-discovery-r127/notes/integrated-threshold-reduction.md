# Integrated singularity-threshold reduction — PREFREEZE / no nominee

This is a feasibility calculation, not a frozen theorem, author-proof intake, correctness/contribution verdict, or count. The pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and all operative upstream proofs are stipulated true. The only developed family is uniform Cartier sections/klt complements and local singularity thresholds. The class-group/Iwasawa catalogue screen was null. There is no third direction.

## 1. Exact source inputs and their already available operations

The pinned **Uniform Cartier sections for Fano type contractions**, introduction `thm:main`, fixes d>0 and epsilon>0 and supplies tau(d,epsilon)>0. The input is an epsilon-lc rational pair (X,B) of dimension d over an algebraically closed characteristic-zero field, a projective contraction f:X->Z of normal integral quasi-projective varieties with connected fibres, dim Z>0, X of Fano type over Z, and -(K_X+B) nef over Z. For each closed z there is a neighbourhood U and a nonzero effective Cartier D through z such that (f^(-1)U,B+tau f*D) is lc. The divisor and U depend on the example; tau is qualitative and independent of boundary denominators, canonical index and polarization. The real-boundary extension is over C. None of these quantifiers is weakened here.

H-reduction was read in full, including its actual complete-section saturation, canonical cover, signed anti-canonical algebra, finite cyclic quotient discrepancy, pinning input, rationalization, change of field, and both concluding proofs. In particular H650–710 is already the exact ideal/general-section operation: on a log resolution write m_z O_Y=O_Y(-F); the ideal threshold is the minimum A(E)/ord_E(F); a general linear combination of generators has divisor F+H with basepoint-free transverse residual H. For coefficient below one, the fixed inequalities and the residual coefficient give lc on the whole inverse image. Conversely v(m_z O_X)<=v(f*g) for g in m_z, so one admissible section proves the ideal inequality. One must not invert this comparison for an arbitrary prescribed g.

The birational theorem is proved by the entire eigenspace saturation obstruction, not by bounding the canonical index. Failure gives all-character-degree order inequalities, and G-pinning contradicts them through increasing algebraically independent directions. G's exact statement and final termination proof were read; its intermediate induction and A–F were acquired but not fully read. This is an explicit reading limit, not a truth audit.

The pinned companion **Bounded klt complements for Fano contractions**, introduction `thm:main`, supplies a bounded klt complement index N(d,epsilon) for boundary-zero epsilon-lc Fano contractions in algebraically closed characteristic zero. Its `cor:finite-coefficients`, over C, supplies monotonic klt complements for finite rational coefficient sets, Fano type, and nef negative adjoint. Main wrapper, exact introductory statements, the complete reduction proof, and the final rank-growth completion were read. The other internal estimates were not all acquired/read. N(K_X+Lambda) is integral Cartier and locally linearly trivial. This bounds the adjoint with its chosen boundary, not the index of K_X alone, a local embedding dimension, or the length of a parameter quotient.

## 2. Strongest primary and original-history composition

Chen, **Boundedness of klt complements on Fano fibrations over surfaces**, actual retained arXiv2403.01154v4 (9 September2025), Theorem1.6, equates the general finite-rational-coefficient klt-complement assertion, its zero-boundary birational case, the general Cartier assertion, its zero-boundary birational case, and the identity-contraction assertion. The actual proofs in sections3–6 were read, as were Lemma2.17 and Corollary2.19. Thus passing between these formulations is already paid, including the generalized-base route, plt extraction/lc complements, MMP, fixed systems, general members and globalization in a common system. The proof uses transitive Birkar, BCHM, HLS and canonical-bundle-formula results that were not all freshly read. It is not a complete primary-chain audit. The v4 proofs were read before this derivation. A late version check corrected an erroneous same-size-implies-identical assertion: the v5 PDF has different bytes and a 19September2025 v5 header. A complete whitespace-normalized extracted-text diff changes only the arXiv version/date line. This is late text-comparison evidence, not a full independent semantic or glyph-level read of v5.

The original C136 statement and proof (I136178–190) and its full I13946–60 audit were read. For a supplied global klt N-complement on an affine base, integrality gives discrepancy gap1/N. The point-ideal operation handles an arbitrary finite set with one general function; an average gives gap1/(2N), and the principal perturbation preserves a uniformly bounded complement index. There is no gluing of independent local complements. We do not renominate this construction or erase its hypothesis of a supplied common complement.

Other scoped original reads: r25/screen-037 describes an unrelated next gap below the ODP normalized-volume endpoint, with its arbitrary-klt and hypersurface distinctions intact; it is not pursued. AB194/r10's exact scope is an all-characteristic-p/all-complete-local-ring/all-short-complex Dutta-multiplicity inequality, not a characteristic-zero upper bound on finite-map degree. Its proof was not read or used. I28's actual filtered finite-normalization calculation was read, retaining its associated-graded, completeness and surface hypotheses; we do not retry its nonconical SmallCM target. F004's full original cyclic-action proof was read: its nonlinear affine-five-space cancellation/stabilization result differs from the linear three-dimensional isolated quotients below. No old scope or disposition is changed.

## 3. What a uniform threshold really pays in local algebra

For the identity contraction, the source yields

    A_(X,B)(v) >= tau(d,epsilon) v(m_x)

for every divisorial valuation centred at x (and the corresponding inequalities on a neighbourhood). Consequently, for any ideal a with m_x^L contained in a,

    v(a) <= L v(m_x),
    lct_(X,B)(a) >= tau(d,epsilon)/L.

Likewise, for 0<=t<tau, subtracting t v(m_x) preserves the fraction 1-t/tau of every starting discrepancy. The inequality is homogeneous in v; the epsilon gap itself is imposed on primitive prime orders. These are routine valuative consequences, not new findings.

There is a stronger compatible composition than selecting one hypersurface repeatedly. Let R be an equicharacteristic local ring of dimension d with infinite residue field, with maximal ideal m. The standard graded algebra gr_m R has dimension d. Choose d general linear homogeneous parameters in its degree-one piece and lift them to g_1,...,g_d in m. With q=(g_1,...,g_d), the finite-dimensional graded quotient means that, for all sufficiently large n,

    m^(n+1) = q m^n + m^(n+2).

Nakayama applied to m^(n+1)/(q m^n) removes the last term and gives m^(n+1)=q m^n. In particular q is m-primary. Applying any valuation centred at m gives

    (n+1)v(m) = v(q)+n v(m), hence v(q)=v(m).

This directly proves equality of ideal thresholds without substituting a possibly worse single chosen equation. Over a completed Cohen–Macaulay complex local domain, the parameters give a finite map from C[[t_1,...,t_d]], t_i->g_i, and the ring is free of rank length(R/q)=e_m(R). For the equality of multiplicities, iterate the reduction identity to sandwich q^n and m^n up to a fixed shift; the Hilbert polynomials have the same leading coefficient. For a parameter regular sequence in a Cohen–Macaulay ring, the length of R/q^n has leading coefficient length(R/q)/d!, giving the displayed rank.

The standard finite/free step can be seen directly: lift a residue basis of R/q to R and use completeness to obtain a surjection from a free power-series module. A parameter sequence is regular in a Cohen–Macaulay local ring. Reduce successively modulo t_1; Tor_1 vanishes because multiplication by t_1 is injective. Induction shows the reduction is an isomorphism, and Nakayama kills its kernel. Algebraic independence of the parameters follows also from finiteness and dimension. Thus the source plus the usual reduction argument really supplies a full parameter ideal with the same threshold. It is not necessary to leave the simultaneous-parameter step as an unspecified gap.

What is absent is an upper bound on its colength/rank. The actual de Fernex–Ein–Mustata primary proof, arXiv math/0205171v1, Theorems1.1–1.2, gives for an m-primary ideal I in a **smooth** n-dimensional local ring

    e(I) lct(I)^n >= n^n.

The proof uses a Newton-polyhedron supporting facet, arithmetic-geometric mean, flat degeneration and semicontinuity, followed by powers of I. It is a lower bound on multiplicity. Reversing its direction is invalid; moreover its smooth ambient ring hypothesis is essential to that exact statement. A lower bound on lct cannot yield the proposed upper bound through this inequality.

## 4. A complete terminal-quotient diagnostic

For each integer r>=2 work over C and let mu_r act on A^3 with weights (1,-1,1):

    zeta.(x,y,z)=(zeta x,zeta^(-1)y,zeta z).

Let X_r=A^3/mu_r, o the image of0, and R_r its completed local ring. Every nonidentity element fixes only0, so the quotient is quasi-etale and X_r is smooth away from o. The invariant monomials are exactly x^a y^b z^c with a+c-b=0 mod r. The invariant subring of the normal domain is normal (an integral element of its fraction field is integral upstairs and then invariant).

Reid's actual toric discrepancy proof and quotient criterion, YPG sections4.2–4.11, printed370–376, were read from the scan. The nonzero residues for the k-th group element, 1<=k<r, have age

    k/r +(r-k)/r +k/r = 1+k/r >1.

The criterion therefore makes X_r terminal, in particular 1-lc globally. This is a classical example, not a new singularity construction. The identity X_r->X_r is a Fano type contraction in the source's sense: the zero boundary is klt, and relative ampleness/nefness for the identity is local on the base (any line bundle is identity-ample). It is projective and has positive-dimensional normal affine base. Thus these are genuine inputs at fixed d=3, epsilon=1, not examples outside the stipulated theorem.

The canonical character is1, so the local canonical index is r. For completeness, a power of dx wedge dy wedge dz descends without divisor exactly when that character becomes trivial. If a smaller power were locally generated downstairs, its upstairs ratio to the standard form power would be an eigenunit at the fixed point. Evaluating a unit at0 forces trivial character. Thus the index cannot be reduced by a nonconstant eigenunit.

### All invariant generators and the full Hilbert function

A minimal generating set for the invariant maximal ideal is

    xy, yz, y^r, and x^(r-i)z^i for 0<=i<=r.

There are r+4 generators, not r+3. To see generation, remove xy or yz until either y is absent or both x,z are absent. The remaining monomial is respectively a product of degree-r monomials in x,z or a power of y^r. None of the displayed monomials is a product of two positive-degree invariants: xy,yz have degree2 and no degree1 invariant exists; with y absent the smallest positive invariant total degree is r; the pure y case is analogous. Distinct invariant monomials are linearly independent. Hence

    dim_C m/m^2 = r+4.

One can compute the entire Hilbert function, so this is more than a failed bound inferred from a large generator list. Put s=a+c. For an invariant monomial, s-b is divisible by r. A factorization into generators has p mixed factors xy/yz, u factors of degree r in x,z, and v factors y^r, satisfying

    s=p+ru,  b=p+rv.

Its length is (s+b)/r+p(1-2/r), maximized at p=min(s,b). That endpoint is feasible: pair all available y with x or z, then split the remaining x,z degree into blocks of size r. For r=2 every feasible p gives the same length. Therefore its exact m-adic order is

    nu(s,b)=min(s,b)+|s-b|/r.

For each s there are s+1 choices of (a,c). Count the monomials of order<q, q>=1. In the half s=b+rk, k>=0, they have b+k<q, with multiplicity b+rk+1. The other half b=s+rk, k>=1, has s+k<q, with multiplicity s+1. The elementary triangular sums give

    length(R_r/m^q)
      = (r+2) binom(q+1,3) + binom(q+1,2).

This holds also in the completion, since each quotient has the same finite monomial basis. In particular

    e_m(R_r)=r+2.

No asymptotic Newton-polyhedron assertion or unproved saturation estimate is needed for this exact calculation.

The ring is Cohen–Macaulay without importing a general invariant-theory theorem. Over A0=C[[x^r,y^r,z^r]], R_r is free on the invariant monomials with 0<=a,b,c<r; there are r^2 of them, one b residue for each a,c. Decompose each exponent into a residue and a multiple of r to prove the free decomposition. Thus x^r,y^r,z^r are a regular parameter sequence, and depth=dimension=3.

For *any* finite local map C[[t_1,t_2,t_3]]->R_r with residue field C, its parameter ideal q is contained in m. Cohen–Macaulayness makes R_r free over the parameter ring as in section3. Its rank is length(R_r/q), which is at least

    dim_C R_r/(m^2+q) >= 1+(r+4)-3 = r+2.

Generic reductions of m attain rank e_m(R_r)=r+2 by section3. Thus the minimum rank of such a finite local presentation is exactly r+2. The explicit map via x^r,y^r,z^r has the larger rank r^2; it is not being confused with the minimum. This is an elementary diagnostic computed from classical quotient data, not a nominated theorem or new-to-literature claim.

## 5. The threshold is good despite the large finite-map degree

Pulling the maximal ideal to A^3 gives the monomial ideal

    I_r=(xy,yz,y^r,(x,z)^r).

Because the quotient is finite crepant and has no branch divisor, the ideal threshold downstairs equals the threshold upstairs. On normalized birational covers, A_up(w)=e A_down(v) and w(I)=e v(m); both ratios are unchanged. Conversely every divisorial order downstairs extends, and a divisorial order upstairs restricts divisorially under a finite extension. This supplies both inequalities, not an assumption of injectivity for restriction.

Howald's actual Main Theorem and its complete proof in arXiv math/0003232v1 give the Newton-polyhedron multiplier ideal formula. Equivalently the ideal threshold here is the infimum, over nonzero nonnegative weights alpha,beta,gamma with positive ideal order, of

    (alpha+beta+gamma) /
    min(alpha+beta, beta+gamma, r alpha, r gamma, r beta).

The mixed degree-r monomials add nothing smaller than min(r alpha,r gamma). Normalize the denominator to1. Then alpha,gamma,beta>=1/r, alpha+beta>=1, beta+gamma>=1. At fixed beta the minimum numerator is

    beta+2 max(1/r,1-beta).

It decreases until beta=1-1/r and increases afterwards. The value there is1+1/r, attained at (alpha,beta,gamma)=(1/r,1-1/r,1/r). These are rational weights defining a divisorial ray. Consequently

    lct_(X_r)(m_o)=1+1/r.

This is an **ideal** threshold. It need not be at most1. We use Howald's main multiplier formula/proof, not a capped expression for a single divisor; the early preprint's surrounding Example5/6 wording is not used to impose such a cap. The publisher PDF attempt returned403, so no assertion of published-byte verification is made.

There is also an explicit good *Cartier divisor*: g=xy is invariant, and upstairs div(g) is the union of two transverse coordinate planes. Hence (X_r,t div(g)) is lc exactly for t<=1, by finite crepant descent. Thus a coefficient1 section already exists uniformly, with its exact whole-neighbourhood behaviour, even though the minimum finite local degree tends to infinity. Generic parameter ideals q retain the ideal threshold1+1/r by section3 and simultaneously have length r+2. This is the strongest parameter-ideal composition, not just a poor choice of one section.

## 6. Even the bounded-complement route is fully present

The examples do not evade the complementary source theorem. They possess a uniform **explicit klt2-complement**. Let

    h=xz+y^(2r-2).

Both terms have character2, and the standard canonical form omega has character1. Put D=div(h) upstairs. The ideal J=(xz,y^(2r-2)) has, by the same monomial calculation, threshold1+1/(2r-2)>1. On a resolution its general two-term member has fixed ideal divisor plus transverse residual. Coefficient1 is lc, and coefficient1/2 is klt, including outside the base locus. All combinations with both coefficients nonzero are carried to h by diagonal scalings over C. Thus (A^3,D/2) is klt.

Let D_X be the effective Weil divisor whose crepant pullback is D; it exists since D is invariant as a divisor and the quotient is unramified in codimension1. The rational2-canonical form omega^2/h is invariant and descends; its divisor is -D_X. Hence

    2(K_(X_r)+D_X/2) ~ 0

is integral Cartier. Finite crepant descent gives (X_r,D_X/2) klt. This is the uniform index2 complement, even when r is odd and D_X is not Cartier. The assertion concerns its adjoint, so it is consistent with the canonical index r. Integrality of that adjoint makes all its positive log discrepancies lie in (1/2)Z, giving a gap at least1/2 for the complemented pair as well.

Accordingly, trying the full compatible composition—uniform Cartier sections, point ideals, finite parameter reductions, bounded klt complements and discrepancy integrality—does not produce a uniform finite presentation degree under just the original d,epsilon hypotheses. In this exact class the target bound is false. It cannot be revived by simply retaining the newly supplied complement index: that index is already2 throughout the examples. An extra hypothesis or a different conclusion would define a different problem, and none is substituted for the old or provisional scopes here.

## 7. Result of the research attempt

Paid operations: the entire source point-ideal/general-section and field-change reduction; Chen's equivalences and the original finite-point common-complement composition; general parameter reductions retaining every valuation order and threshold; classical monomial multiplier and quotient discrepancy calculations; the complete invariant-ring Hilbert-function, colength, degree and explicit-complement diagnostic above.

No nonroutine source-dependent operation closed beyond these compositions. In particular there is no proof-feasible new uniform local finite-presentation theorem to freeze. The unrestricted degree bound tested here is disproved by a classical family even after the strongest threshold/complement integration. A different substantial singularity invariant or construction would require a concrete new operation; no such result is asserted, and no vague parked obligation is offered as progress toward acceptance.

PREFREEZE / no nominee. This is neither universal impossibility nor exhaustion of the source family. It does not claim priority for the diagnostic or rename a failed old target. All old frozen scopes, proofs, conditions and dispositions—including T360S147, H138 and T185R144 full PASS/TECHNICAL with conditions discharged—remain unchanged. The parent alone integrates, reviews and counts. Read limits and artifact authentication are separate from mathematical gates.
