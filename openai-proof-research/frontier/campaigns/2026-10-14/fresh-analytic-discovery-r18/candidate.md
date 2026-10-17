# A natural IID sampler for strongly Rayleigh laws on countable sets

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

**Author-level complete proof proposed; independent proof and contribution
review pending. Counted=false.** The original target CS is retained in
full. Its immutable scope SHA256 is
`b1327efb9564d7ddf64d2bcb248aa5d70a699f3ee63ad4d364de7d5f2abc4877`.

## 1. Statement and premises

For every finite or countably infinite set I there is a jointly Borel map

    Phi_I : SR(I) x [0,1]^I -> {0,1}^I

sampling every strongly Rayleigh law nu exactly from independent uniforms,
such that for every bijection sigma:I->J and every label input u,

    Phi_J(sigma_*nu, sigma u) = sigma Phi_I(nu,u).             (CS)

Here `(sigma u)_(sigma i)=u_i`. SR(I) has the relative Borel structure in
the probability laws on the compact metrizable product {0,1}^I. The empty
index set has the unique map. The rule is independent of any group or
chosen graph. In particular it commutes on every input with every element
of the full permutation stabilizer of nu, not only with a countable
selected subgroup.

We use the pinned family231 source at revision
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, with its truth stipulated:

* `lem:sr-response`: for every finite strongly Rayleigh law and every
  positive exponential field tilt, the row of derivatives of a mean is
  its covariance row, with absolute row sum at most 1/2. Its proof also
  gives nonpositive off-diagonal covariances and
  sum_(j!=i) -Cov(X_i,X_j) <= Var(X_i).
* `prop:brownian-sampler`: on any countable index set, any fixed finite
  increasing exhaustions whose finite-tilt means have a common L-Lipschitz
  bound yield the stated limsup-drift/Picard/readout sampler. Independent
  Brownian input produces the full target law.
* `lem:inverse`: the same bounded Lipschitz drift has a unique solution
  for every product of continuous paths, defined by Picard iteration,
  Borel and equivariant under relabelings intertwining the drift.
* `lem:edge-noise`, specifically its one-uniform-to-Wiener-path subproof:
  a fixed Borel function beta:[0,1]->C([0,infinity),R) maps uniform
  measure to Wiener measure, with values defined on every input.

Negative association of finite strongly Rayleigh laws is the classical
Borcea–Brändén–Liggett Theorem 4.9 (arXiv:0707.2340v2). The independence
calculation below is Alishahi–Barzegar–Zamani Proposition 2.2 specialized
to zero cross covariances; it is included explicitly, not claimed new.
The source Brownian theorem is used on individual components. We do not
silently weaken its exhaustion hypothesis on the whole set I.

## 2. Independence determined by the covariance graph

Fix nu in SR(I) and write X for its coordinate process. For distinct i,j
put c_nu(i,j)=-Cov_nu(X_i,X_j). All these numbers are nonnegative. For
every finite F containing i, the row bound gives

    sum_(j in F\{i}) c_nu(i,j) <= Var_nu(X_i) <= 1/4.

Taking the supremum over finite F proves

    sum_(j!=i) c_nu(i,j) <= 1/4.                              (2.1)

Let G_nu be the simple undirected graph on I with edge ij precisely when
c_nu(i,j)>0. Its degree may be infinite. Let C_nu(i) be the connected
component of i, with graph connectivity meaning a finite edge path.

For disjoint finite A,B and events E in sigma(X_A), F in sigma(X_B),
put U=sum_(i in A) X_i and V=sum_(j in B) X_j. Each function
U+1_E, U-1_E, V+1_F, V-1_F is coordinatewise increasing: changing one
bit upward adds one to U or V, while an indicator changes by at most one.
Negative association applied to both equal-sign pairs gives

    2 Cov(U,V) + 2 Cov(1_E,1_F) <= 0.

Applied to both opposite-sign pairs it gives

    2 Cov(U,V) - 2 Cov(1_E,1_F) <= 0.

Consequently

    |Cov(1_E,1_F)| <= -Cov(U,V)
                     = sum_(i in A,j in B) c_nu(i,j).       (2.2)

If no edge joins A to B, the right side is zero. In particular any
cylinder event in one collection of covariance components is independent
of any cylinder event in a disjoint collection. A monotone-class argument
extends this independence to their generated sigma-fields. Iterating
across finitely many distinct components and then using cylinder
determination proves the full factorization

    nu = product_(C a component of G_nu) nu_C,               (2.3)

where nu_C is the C-marginal. There are at most countably many components.
Each nu_C is strongly Rayleigh because its finite marginals are.

Only entire covariance components are independent. An isolated zero
covariance between two sites inside a larger component is not being used
as conditional independence after observing other coordinates.

## 3. Canonical finite observations

For each integer n>=1 define the threshold graph G_nu,n by

    ij is an edge iff i!=j and c_nu(i,j) >= 1/n.

Equation (2.1) implies that every vertex has degree at most floor(n/4).
In particular the radius-n closed graph ball

    S_n^nu(i) = {j: distance_(G_nu,n)(i,j) <= n}              (3.1)

is finite and includes i. The graphs increase with n, as do the allowed
path lengths; hence S_n^nu(i) is increasing in n. Their union is exactly
C_nu(i). Indeed all their edges are edges of G_nu. Conversely, any fixed
finite positive-covariance path has finitely many positive edge weights;
for n sufficiently large its length is at most n and all weights are at
least 1/n. That path then lies in G_nu,n.

All these definitions are intrinsic to the law. If sigma:I->J is a
bijection, covariance transforms by

    c_(sigma_*nu)(sigma i,sigma j)=c_nu(i,j),

so threshold balls transform exactly, at the same integer n. No ordering
of an infinite stabilizer orbit or random selection from one is required.

## 4. Drift, inverse and output on every input

For finite S subset I, i in I, t>=0 and y in R^I define the finite-tilt
mean by the finite marginal on S union {i}:

    b_(nu,i,S)(t,y)
      = E_nu[X_i exp(sum_(j in S)(y_j-t/2)X_j)]
        / E_nu[exp(sum_(j in S)(y_j-t/2)X_j)].               (4.1)

Both quantities are finite sums, the denominator is strictly positive,
and the ratio is in [0,1]. Define

    b_(nu,i)(t,y)=limsup_(n->infinity)
                      b_(nu,i,S_n^nu(i))(t,y).              (4.2)

The finite marginal is strongly Rayleigh, so the source response lemma
gives, for d=sup_j |y_j-y'_j|<infinity,

    |b_(nu,i,S)(t,y)-b_(nu,i,S)(t,y')| <= d/2.

Take limsups in both directions to obtain the same bound for (4.2),
uniformly in i and nu. The drift is bounded, and its Borel property is
proved below. The source inverse lemma therefore defines, for every
w in product_i C([0,infinity),R), the unique solution

    Z_(nu,i)(w)(t)=w_i(t)+integral_0^t
                            b_(nu,i)(s,Z_nu(w)(s)) ds.     (4.3)

Explicitly Z^0=w and Z_i^(k+1)=w_i+integral b_i(s,Z^k(s)) ds.
The source factorial bound, uniformly in nu, is

    sup_i sup_(0<=t<=T) |Z_i^(k+1)(t)-Z_i^k(t)|
      <= (1/2)^k T^(k+1)/(k+1)! .                          (4.4)

Define W(u)_i=beta(u_i), applying the same fixed all-input Brownian
converter at every site, and set

    Phi_I(nu,u)_i
       = 1{limsup_(m->infinity) Z_(nu,i)(W(u))(m)/m > 1/2}. (4.5)

This formula is meaningful on every input, even when the slopes have no
limit. No null-set selector or group-dependent modification is made.

## 5. The exact output law

Fix a covariance component C. For i in C, every finite set in (3.1) lies
inside C, and their union is C. Formula (4.1), restricted to these sets,
uses only the marginal nu_C and fields on C. Thus the restriction of the
global drift to C is precisely the drift in the source Brownian-sampler
proposition for index set C, target law nu_C, and exhaustions S_n^nu(i).
The finite response bound is 1/2, uniformly in i,n,t as required.

The component of each global Picard iterate equals the component Picard
iterate on C, by induction on k. Passage to the limit preserves this
identity. Therefore the output coordinates on C depend only on the
Brownian input coordinates on C and have law nu_C by the source
proposition. Different components use disjoint families of independent
inputs. Their outputs are independent, so (2.3) identifies the entire
output law as nu. This includes finite components, singleton components,
and deterministic coordinates. No assertion about an uncountable
intersection of almost-sure events is needed.

## 6. Joint Borel measurability in the law and labels

For fixed finite/countable I, each covariance c_nu(i,j) is continuous
in nu, since coordinate cylinders are continuous functions on {0,1}^I.
For fixed i,j,n the assertion j in S_n^nu(i) is a countable union, over
finite paths of length at most n, of finite intersections of the closed
conditions c_nu(a,b)>=1/n. It is therefore Borel.

The set of finite subsets of I is countable. For every particular finite
S, the condition S_n^nu(i)=S is a countable intersection of the preceding
membership predicates and their complements. On this Borel set (4.1)
is a continuous function of nu,t and the finitely many field values.
Since (3.1) is always finite, countable piecewise assembly proves joint
Borel measurability of each finite-stage drift. Taking its countable
limsup proves that (nu,t,y)->b_(nu,i)(t,y) is Borel. These statements use
the relative Borel structure of SR(I), so they require no arbitrary
choice of a coordinate enumeration in the actual formula.

For completeness SR(I) itself is closed: every finite marginal map is
continuous; coefficient limits of stable polynomials are stable or zero
by the multivariate Hurwitz closure property, while normalization at
the all-one vector excludes zero. Intersect these closed conditions over
the countably many finite marginals. This familiar closure is also in
BBL Proposition 3.1(3). Thus the law parameter space is standard Borel.

Evaluation (t,z)->z(t) on the product path space is continuous.
Inductively, if (nu,w)->Z^k_nu(w) is Borel then the bounded integrand
(nu,w,s)->b_(nu,i)(s,Z^k_nu(w)(s)) is Borel. Parameter integration gives
Borel rational-time evaluations of Z^(k+1). Its paths are continuous,
and rational-time evaluations generate the path-space Borel structure,
so the next iterate is Borel. Equation (4.4) gives a coordinatewise
continuous-path limit, with Borel rational-time evaluations, proving
joint Borel measurability of (nu,w)->Z_nu(w). The fixed coordinatewise
map W and the countable limsup predicate (4.5) finish the claim.

## 7. Exact naturality and the consequences

The covariance identity in section 3 implies the exact threshold-ball
identity. Relabeling a finite sum in (4.1) therefore gives, for all fields,

    b_(sigma_*nu,sigma i)(t,sigma y)=b_(nu,i)(t,y).

This passes to the limsup. By induction every Picard iterate intertwines
sigma, and its limit does too. The fixed coordinatewise converter beta
intertwines sigma on every input, as does the coordinatewise readout.
Equation (CS) follows for every nu and every u.

If a group acts on I preserving nu, apply (CS) to each of its permutations.
This proves the full arbitrary-action consequence, with one map for the
full law stabilizer and no countability restriction on the group. The
input IID law is always the product uniform law on the same index set I.

For a Hermitian positive contraction K on l2(I), the determinantal law
has strongly Rayleigh finite marginals: finite compressions are positive
contractions, their principal determinants give the same inclusion
probabilities, and inclusion-exclusion identifies the marginal law.
BBL Proposition 3.5 gives its strong Rayleigh property. Applying CS to
the resulting law gives the determinantal consequence, including
singular/projective kernels and law symmetries not preserving the chosen
kernel. This finishes the proposed full proof.

## 8. Why the construction is not an arbitrary-law sampler

Uniform measure on the four even-parity configurations in {0,1}^3 has
all pair covariances zero, so its covariance components are singletons,
yet its coordinates are not jointly independent. It is not negatively
associated: with E={X_1=1}, F={X_2=1 or X_3=1}, both increasing and
depending on disjoint sites, P(E and F)=1/2 while P(E)P(F)=3/8.
Thus (2.2), not pairwise decorrelation alone, is indispensable.

Conversely an infinite product Bernoulli law has singleton components
and a full permutation symmetry when all marginals agree. No finite
equivariant subsets can exhaust the whole infinite set under this full
symmetry, but singleton component sampling works. This illustrates the
actual scope gained: global equivariant exhaustion is neither presumed
nor manufactured where it is impossible.

## 9. Contribution boundary

The proposed bridge is the canonical, law-dependent component geometry
that makes an all-input decoder natural under arbitrary coordinate
relabeling. Negative association, zero-covariance independence, summable
rows, Brownian observations and the Picard sampler are credited inputs.
The proof above establishes an author-level deduction from them; it does
not independently settle whether this bridge meets the campaign's
substantial-contribution threshold. No count, publication, full Lean
formalization or independent PASS is claimed.
