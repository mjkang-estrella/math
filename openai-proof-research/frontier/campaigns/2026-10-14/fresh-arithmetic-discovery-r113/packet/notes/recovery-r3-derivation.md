# r3 continuation: the weighted trace-slice calculation

Status: PREFREEZE / no nominee. This is a new recovery calculation, not a
replacement of the r1/r2 records and not a frozen full-scope theorem. It
addresses their displayed (B) and (C) in the SAME arbitrary-order sextic
family. The calculation below completes that sufficient arithmetic interface
at the level of this discovery derivation. It does not constitute a submitted
full author proof of the equidistribution target or an independent correctness
gate. The construction follows the actual proof in the pinned quartic
companion, additive.tex, freshly read in full during r3. In particular the
three cases, use of a signed original profile sum, inverse-order congruences,
and adjugate polynomial count are credited source operations.

## Data and the precise interface

K is a totally real degree-six field with no proper intermediate field;
M=O_K; O is ANY order in K. Put D=Disc(K), q=[M:O], Delta=Dq^2 and
X=q sqrt(D). Embeddings may have any order. Let S contain the primes dividing
Dq and 2,3,5,7. Extra fixed primes may be included. All constants below may
depend on the fixed real test data and fixed nonzero integer m, but not on
K,O, embeddings, centers, or permitted shrinking scales.

At p use the trace character and its self-dual additive measure; vol(M_p)
=|D|_p^(1/2). Let f_p be the product density of independent Haar-probability
variables x in O_p and y in O_p^vee. Its transform is

    gamma_p(A) = [O_p : O_p intersect A^-1 O_p]^-1.

For A with a zero component this formula means the preimage lattice condition,
not division by that component. Indeed integration first over y is the
indicator Ax in O_p. For invertible A, change of variables gives

    gamma_p(A)=|N A|_p^-1 gamma_p(A^-1).

For every s in Z_p, gamma_p(A+s)=gamma_p(A), since O_p is an order.

Use five real linear coordinates u on Tr z=m, completing them with Tr z to a
linear map of absolute determinant one. Both deleted-coordinate charts and
a chart with one coordinate sum_{j in J} z_j for a nonempty proper J have
this property. Set

    phi(z)=Phi((u(z)-c)/r) chi(Tr z),
    A_phi=(product_{j=1}^5 r_j) integral Phi,

where Phi is a fixed nonnegative smooth compactly supported majorant and
chi(m)=1, supp chi is inside (m-1/3,m+1/3). Supports lie in a fixed compact
region, and X^-tau <= r_j <= r_* for a fixed upper bound. The claim derived
here is

    sum_{z in K, Tr z=m, z in M_p (p notin S)}
        phi(z) product_{p in S} f_p(z)
      = A_phi product_{p in S} d_p(m) + O(X^-epsilon),       (R3.1)

where d_p is the trace density and its finite products are bounded above and
below by absolute positive constants. This implies the old upper bound (C).
The much larger full target still includes all complete Picard packets, all
signs, order discriminant tending to infinity including fixed K, Haar
convergence and no escape. (R3.1) is not offered as a substitute nomination.

## Local checks, including the missing small-prime modulus

Let h_p be an integral maximal-order ideal specifying the exact pole orders
of A, H_p=N h_p, and p^g=[h_p:h_p intersect O_p]. Select s in {0,...,6}.
At p>7 one can avoid the at most six residues forbidden by the integral
components. Thus alpha=A+s has norm |N alpha|_p=H_p and beta=alpha^-1 in h_p.
At p<=7 select s such that each integral component has v_p(A+s)<=2, where
v_p extends the normalized valuation of Q_p. Each component forbids at most
one of the seven choices: two forbidden choices would have a difference
with valuation >2, impossible for two distinct integers between 0 and 6.
Pole components are unchanged. Hence beta in p^-2 h_p and

    p^-12 H_p <= |N alpha|_p <= H_p.

If j is the least nonnegative integer with p^j beta in O_p, the matrix of
multiplication by beta on an O_p basis has smallest Smith exponent -j when
j>0. This follows because beta O_p subset p^-j O_p is equivalent to beta
in p^-j O_p: use 1 in O_p and multiplication closure. Consequently

    |gamma_p(A)| <= C_p H_p^-1 p^-j,
    C_p=1 (p>7), C_p<=p^12 (p<=7).                         (R3.2)

This is stronger than the square-root estimate used below.

The shell restriction gamma_{p,h} extended by zero is invariant under
p^{4(g+3)} h_p^-1. To check this, for a translation t in that lattice the
pole shell and the chosen shift valuation bounds are unchanged; 1+t beta
is a maximal-order unit and

    beta' - beta = -t beta^2/(1+t beta)
                  in p^{4(g+3)-4} h_p subset O_p.

Here p^g h_p subset O_p, as follows from the index. Multiplication by beta
and beta' has the same containment condition on O_p, and their alpha norms
are equal. This proves the asserted period, including zero extension.
The O_p period of gamma also preserves its shell. Its inverse Fourier
transform K_{p,h} is therefore supported on

    p^-4(g+3) h_p d_pifferent^-1 intersect O_p^vee.

There is a uniform bound |K_{p,h}|<=C_p vol(M_p), since the shell has volume
at most H_p vol(M_p) and (R3.2) bounds its transform by C_p/H_p.
If g=0 and p>7 then beta in h_p subset O_p, so gamma_{p,h}=H_p^-1 on its
shell. In each component of residue cardinality q_v, its inverse factor is
1_{d_v^-1} when h_v=0, and when h_v>0 is

    1_{P_v^{h_v} d_v^-1}
       - q_v^-1 1_{P_v^{h_v-1} d_v^-1}.

Multiply these factors and vol(M_p). At a boundary component, i.e. in the
larger support but outside the smaller one, this saves q_v^-1. These are
not independence assumptions about O_p; g=0 is exactly what made the
Fourier shell constant. At an output with all components nonzero only
finitely many inverse shells survive, by their support conditions. Fourier
inversion on expanding compact open sets identifies their sum with f_p
there: the product pushforward is locally constant near such an output,
and convolution with a sufficiently small open-subgroup probability equals
that density. All global nonzero field elements meet this condition.

Here is the detailed small-prime congruence needed later. Choose a generator
i of h_p and put x=i(A+s). At a small prime x is integral, is a unit on
pole components, and has 0<=v_p(x)<=2 on the others. Put y=p^2 x^-1 in M_p.
Choose a primitive linear form ell with

    ell(i^-1(h_p intersect O_p)) subset p^{g'} Z_p,
    g'>=g/6,

using the largest Smith exponent. From p^j beta in O_p and beta=i x^-1,
p^j i y=p^2(p^j beta) lies in h_p intersect O_p. Thus
ell(y)=0 mod p^k for every 1<=k<=(g'-j)_+.

On the permitted locus, x mod p^{k+2} determines y mod p^k, by the identity
for the difference of inverses. Conversely a fixed y mod p^k confines x
to a single residue modulo p^{k-2}, using
x-x'=p^-2 x(y'-y)x'. For k=1 the latter assertion is vacuous and the same
upper count below remains valid. The permitted valuations of x are
determined modulo p^3, hence at modulus p^{k+2}. A primitive linear form
has p^{5k} kernel residues in M_p/p^k M_p. Each admits at most p^24 lifts
of x modulo p^{k+2}. Thus the retained fraction is at most

    p^{5k+24}/p^{6(k+2)} = p^{12-k}.                       (R3.3)

The constant p^12 is harmless at the four fixed small primes. The joint
CRT modulus uses TWO additional powers of each participating small prime,
not the single additional power in the cubic source. At p>7, x is a unit;
inversion permutes finite-algebra units and the same fraction is simply
p^-k at modulus p^k, including ramified residue algebras with nilpotents.

## Finite global expansion and Poisson normalization

For a profile h supported on S let H=N h and G=product p^g. The exact index
identity gives G<=q<=HG. Let T be the product of boundary prime-ideal norms
at primes where g=0 and p>7. The preceding supports and the nonzero norm
of z in the fixed real box give

    H <= C D G^96 T,   T <= (rad S)^6 <= C X^12.           (R3.4)

Indeed 4(g+3)<=16g for g>0; multiplying by degree six yields 96g. The
small primes with g=0 cost a fixed constant. Dropping h and the nonnegative
boundary support exponents puts every point in a fractional ideal a_h
with N(a_h)^-1<=C D G^96. The global inverse product has magnitude at most
C T^-1 and, more weakly, C T^-1/2. Thus these bounds do not require a
positive inverse shell.

Since D<=X^2 and G<=q<=X, (R3.4) gives H<=C X^110, so H<=X^111 for large
X. There are X^o(1) profiles: for fixed u>0 Rankin bounds their number by
X^{111u} product_{p in S}(1-p^-u)^-6; |S|=O(log X/loglog X) follows from
rad S<=C X^2. Choose u arbitrarily small. This bound is uniform.

Let eta_h have factor K_{p,h} at S and 1_{M_p} elsewhere. The original sum
in (R3.1) is exactly the finite sum of S_h=sum_{z in K} phi(z) eta_h(z)
for H<=X^111. All finite factors have integral trace support, and only the
integer m meets supp chi. Each eta_h is Schwartz--Bruhat, and its global
original sum is finite. Use self-dual measures: the real covolume of M is
sqrt(D) and product_p vol(M_p)=D^-1/2. The field has adelic covolume one,
so Poisson gives

    S_h=sum_{A in K} phi_hat(A) product_{p in S} gamma_{p,h}(A)
                              product_{p notin S} 1_{M_p}(A).   (R3.5)

There is no extra D, q, or trace-plane covolume in this identity. Outside
S the algebra is unramified, so its integral indicator is self-dual.

## All nonscalar profiles: completing the old (B)

Set

    d=e=10^-4, e1=e/100=10^-6, e2=e1/100=10^-8,
    w=e2/1000=10^-11, tau=w/100=10^-13,
    epsilon=e2/4=1/(400000000), Y=X^w.

A fractional ideal of norm H^-1 has covolume sqrt(D)/H, first minimum
at least c H^-1/6, and the following count in the radius-Y ball:

    C [sum_{k=0}^5 Y^k H^{k/6} + Y^6 H/sqrt(D)].          (R3.6)

The nonzero norm inequality proves the first-minimum bound. A basis of
bounded orthogonality defect, Cramer's rule and the successive-minimum
product prove the count; the same argument bounds every basis coefficient
by C Y H^1/6. This is the fixed-dimensional lattice argument in the source,
with dimension six.

Derivative bounds give |phi_hat(A)|<=C_r X^{r tau}(1+|A|)^-r.
The rough count O(R^6 H) and |product gamma_h|<=C/H show that the tail
|A|>Y per profile is at most

    C_r X^{r tau+(6-r)w}.

For r=1000 the exponent is -0.984 e2. The X^o(1) profile count can be
absorbed with a margin beyond epsilon. In the retained ball use
|phi_hat|<=C. Frequencies belong to h^-1.

Case 1: D>=X^d. Every nonscalar A generates K by primitivity. HA is integral
because the integer H annihilates M/h. Comparing discriminants gives
D<=C(HY)^30, hence H>=c X^{d/30-w}. Multiplying (R3.6) by H^-1 gives for
k=0,...,5 the exponents

    -(1-k/6)d/30 + (1+5k/6)w,

and for the last term 6w-d/2. Each is strictly below -epsilon with ample
margin. Empty nonscalar balls contribute zero. No prime-degree assumption
was silently used: primitivity supplies generation in degree six.

Case 2: D<X^d and G<=X^e. The exact equality X=q sqrt(D) gives
q>=X^{1-d/2}>=X^{1/3}, so H>=X^{1/3-e}. Estimate S_h on the original
side. Its supporting fractional ideal has at most C D G^96 points in the
fixed real box, by the first-minimum bound. At each such point (R3.4) and
the weaker boundary saving bound its inverse weight by
C (D G^96/H)^1/2. Therefore

    |S_h| <= C X^{-1/6+(3/2)d+(289/2)e}.                  (R3.7)

Subtract scalars rather than absolute-valuing the whole nonscalar series.
A scalar in this profile has S-denominator t=H^1/6 (otherwise there are no
scalars), is integral outside S, and has weight exactly t^-6=H^-1.
There are O(1+Y H^1/6) scalars in the ball; their contribution is
O(H^-1+Y H^-5/6). This has a fixed saving by H>=X^{1/3-e}.
Use the already controlled scalar Fourier tail as well. Poisson now bounds
the absolute value of the full nonscalar sum for this profile by these
three quantities. It is essential that this estimates the signed sum
profile by profile, not the sum of absolute values of its frequencies.

Case 3: D<X^d and G>X^e. For each A choose the local shifts above and let
J=product p^{j_p}. By (R3.2) the coefficient is at most C H^-1 J^-1,
which we weaken to C H^-1 J^-1/2. Frequencies with J>=X^e2 have total at
most C X^{6w-e2/2} per profile, using the rough count.

For J<X^e2, a nonscalar A generates each localized algebra. The full-rank
order Z_p[p^{j_p}(A+s_p)^-1] is contained in O_p. Scaling discriminants
and inverting six conjugates give

    disc(beta_p)=disc(A)/N(A+s_p)^10,
    disc(p^{j_p} beta_p)=p^{30j_p} disc(beta_p).

At primes outside S, A is integral. Multiplication of these rational
valuation inequalities, and |disc(A)|<=C Y^30, gives

    C Y^30 >= |disc(A)| >= c Delta J^-30 H^-10.           (R3.8)

The bounded small-prime norm changes only a fixed constant (indeed their
sign here can be favorable). Since Delta=X^2>=X, this implies
H>=c X^{1/10-3(w+e2)}>=X^{1/20} for sufficiently large X.

Group the remaining frequencies by their shifts and j_p. The number of
groups is X^o(1), using Rankin for J and 7^{|S|} for shifts. A reduced basis
of h^-1 puts each group in a six-dimensional integer cube of side O(L),
where L is chosen comparable to Y H^1/6. Thus

    L>=c X^{1/120},  L^6/H=O(X^{6w}).                     (R3.9)

The local map from these global integer coordinates to x=i_p(A+s_p) is
an affine GL_6(Z_p) map, since i_p h_p^-1=M_p. Set a_p=(g'_p-j_p)_+.
The available congruence product satisfies

    product p^{a_p} >= G^{1/6}/J > X^{e/6-e2}.

This exceeds X^{2e1}. If every available prime is <=X^e1, multiply
available prime powers one factor at a time until reaching X^{e1/2}.
The result M1 lies between X^{e1/2} and X^{3e1/2}. The CRT fractions from
(R3.3) and its large-prime version retain at most C/M1 of all residues at
modulus M1 times a divisor of (2*3*5*7)^2. That modulus is o(L) by (R3.9).
Counting residues in the cube therefore gives at most
C L^6 X^-e1/2 frequencies.

Otherwise an available prime p>X^e1 exceeds 7. In B=M_p/pM_p, the numerator

    P_ell(x)=ell(adj(M_x) 1_B)

of ell(x^-1) is a nonzero polynomial of degree at most five. To see
nonvanishing even with nilpotents in B, the coordinate ring of the vector
space B is the polynomial domain F_p[X1,...,X6]; the norm polynomial is
nonzero at 1; its nonvanishing open set is dense; and inversion is an
automorphism of that open set. A nonzero linear form cannot become the
zero rational function under inversion. Affine GL_6(F_p) coordinate
changes preserve this nonvanishing. Induction in the variables counts
zeros in an integer cube by O(L^6/p+L^5). For side length smaller than p
use distinct coordinate residues; for a larger cube partition each axis
into at most ceil((2L+1)/p) intervals and use the degree bound in each
product. Thus the frequency count here is
O(L^6(X^-e1+X^-1/120)).

Multiplying the last two bounds by H^-1, and using (R3.9), gives exponents
6w-e1/2 and respectively 6w-e1, 6w-1/120. All are less than -epsilon.
The large-J margin e2/2-6w=0.494 e2 is also larger than epsilon. Together
with (R3.7), scalar subtraction and the tail, every case has a strict
margin. The uniform X^o(1) counts of profiles, shifts and exponent lists
can therefore all be absorbed while retaining epsilon=e2/4. This proves
precisely the sufficient nonscalar estimate (B) of the historical notes
for the fixed test family specified above.

## Scalar evaluation and the thin slab

For a scalar with denominator p^k, gamma_p(a)=p^-6k. The trace marginal
is supported on Z_p and its character series converges uniformly, with

    |d_p(t)-1| <= (1-p^-1)/(p^5-1).

The sum of these bounds over primes is finite and each is <1, which
bounds every finite product above and below by positive absolute constants.
The exact real scalar transform is A_phi chi_hat(a), using the chosen
unit-Jacobian chart. A scalar with S-denominator t has H=t^6, weight t^-6,
and lies in t^-1 Z. Rapid decay of chi_hat bounds its summed absolute
contribution by C A_phi t^-5. Removing the profile cutoff therefore costs
at most

    C A_phi sum_{t>X^{111/6}} t^-5 = O(X^-74).

The same bound without the cutoff gives absolute convergence. Apply
one-dimensional Poisson to finite truncations of the trace character
series, then use their uniform convergence and the preceding absolute
bound. Finite places force the trace to be an integer; chi selects m.
The resulting scalar contribution is exactly A_phi product_S d_p(m).
Together with (B), this proves (R3.1), with uniform constants as specified.

Choose a chart whose first coordinate is the required proper partial sum,
one scale comparable to delta and the other four fixed. A fixed majorant
covers a bounded box and slab, with A_phi=O(delta). Whenever delta>=X^-tau,
(R3.1) bounds the density-weighted sum by C(delta+X^-epsilon). Nonzero
m is available in the marked-vector argument by choosing the dual vector
outside both the coordinate hyperplanes and the hyperplane orthogonal
to the chosen ordinary vector. A finite compact cover uses finitely many
such nonzero integers. This retains every packet point.

## Where this leaves the full discovery

Combining this calculation with the historical exact paired unfolding and
local disintegration gives the tube upper bound

    mu_O(tube) <= exp(O(log X/loglog X)) kappa^-1
                    [exp(-t)+X^-epsilon].                (R3.10)

The product of the local unit-mass reciprocals is included in the displayed
subpower overhead. For times between
log(Delta)/(loglog Delta)^(2/3) and
log(Delta)/(loglog Delta)^(1/3), exp(-t)=X^-o(1), so the scales in (R3.1)
are permitted and the power error is negligible. The reciprocal residue
is O(log(3D)), including bounded D, because the source residue proof uses
absence of a quadratic subfield and primitive generators, both available
here. Thus (R3.10) is <=exp(-t/3) eventually, uniformly in the finite cuts.

Fresh r3 reads also checked the prime companion's local/analytic/geometry
proofs and the historical UI145 calculation. The latter is a routine
weighted-norm summation: its q^-1 factor is retained by the exact local
shell identity, and a bounded third shortest-vector-height moment yields
mu{shortest vector<=r}<=C r^3. Its proof applies in degree six because
the only prime-degree uses in the residue/finite-field-count passages are
replaced by primitivity and no quadratic subfield. The ordinary box bound
is O(r^6) in probability limits. These are compatible inputs, not new
contribution evidence.

The arithmetic residual (B)/(C) stated in the r1 notes should therefore no
longer be called simply unproved after r3: it has the displayed derivation.
The remaining full-target obligations are a complete, explicitly assembled
author proof for the arbitrary-order packet with every normalization and
all uses of the source dynamical chain at the new discriminant parameter,
and actual independent scrutiny. In r3 only the specified conditioning,
entropy and combination interfaces and complete assembly were reread;
the full internal product/activity/homogeneous/conditioning chains were
not. No full-scope proof is submitted or frozen here. More decisively for
this discovery's purpose, the completed calculation uses the source's
existing profile/congruence mechanism with fixed-dimensional changes and
an elementary product Fourier model. No identifiable nonroutine operation
or substantial-contribution evidence was established. That is a genuine
stopping point for this selection, not grounds for opening another family,
renaming a supporting result, declaring impossibility, or claiming priority.
