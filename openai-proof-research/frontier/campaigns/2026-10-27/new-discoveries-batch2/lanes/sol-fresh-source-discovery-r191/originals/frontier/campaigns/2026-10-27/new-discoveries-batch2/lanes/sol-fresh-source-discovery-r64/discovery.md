# r64: higher-shift metallic Hankel quasipolynomials — unresolved, credit 0

## Scope and source screen

Three attributed source leads were screened, fewer than the four-target maximum.

1. Takashi Agoh, Integers26 A9 (2026), final real-rooted-polynomial question. Search returned the actual published PDF, but prior r63 context already identifies public Agoh coverage. Retired immediately, no new investment or claimed outcome.
2. Junnosuke Koizumi, Integers26 A28 (20 February2026), Conjecture1 p4: for every positive rational starting value, convergence of the pseudo-greedy gaps to zero implies eventual zero gaps. Actual journal body, latest arXivv1, Lemma4, Theorem3 and Proposition1/proofs read. The journal renumbers the v1 conjecture6 and theorem16. The public working report243 already supplies finite-flat-transient obstructions and a negative-gap summability sufficient condition. A numerator-descent argument would only repeat the source's eventual-nonnegative case. Deferred, no alleged proof or new partial theorem.
3. Selected: Guo-Niu Han and Emmanuel Pedon, arXiv:2610.36132v1, 26October2026, ConjectureC, Section1. Actual latest HTML and abstract history fetched; no journal version is asserted. This is a full all-shift question, distinct from the old already-public higher-shift unboundedness theorem.

The selected source statement is: for EVERY integer n>=1 and EVERY integer ell>=n+3, define F=Phi_n in Z[[q]] by constant coefficient1 and

    q F^2 + ((1+q^n)(1-q)-q(1+...+q^(n-1))) F = 1.

Put Delta_j^(ell)=det([q^(ell+a+b)]F)_(0<=a,b<j), with Delta_0=1. Put rho=2n(n+1) if n is even and rho=4n(n+1) otherwise. For every residue 0<=r<rho there should exist Q_(ell,r) in Q[X], integer-valued on ALL integers, such that

    Delta_(r+m rho)^(ell) = Q_(ell,r)(m) for EVERY integer m>=0.

No bounded degree is specified by the source. Thus an isolated nonzero finite difference cannot refute the conjecture. A complete counterexample would require, for some n,ell,r, proving that this residue sequence is not a polynomial of any degree. None found.

## Closest source and public theorem bodies read early

Actual new-source TheoremsA/B and Algorithm2.3/Theorem2.2 establish periodic H-fractions and determinant values only at ell=n+2. The older2502.05993v2 supplies lower-shift periodicity, contiguity and finite-field periodicity (TheoremF); its Section7.3 proof is a finite-field argument, not a characteristic-zero polynomial-growth theorem.

At immutable observed Omega commit6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3 the Problems/han-pedon-metallic-hankel-unbounded.md body proves old ConjectureE(2), all shifts unbounded. Its explicit final scope list leaves open the full affine n+3 pattern and closed forms for higher shifts. Actual D5 Lean Data, UnboundedTransfer and UnboundedCofactor bodies were fetched and read, as well as the Blueprint theorem bodies. These are separately identified in provenance; the saved r57 omega-D5 tree is a BLUEPRINT tree and is not relabeled a Lean tree. No source compilation or audit of those public Lean files was performed.

The public dual-number proof computes monodromy modulo x^2. Its `monodromy` subproof acts on an arbitrary two-component state, not only the initial vector. In particular it supplies the identity constant matrix. This is significant prior coverage: the underlying transfer mechanism is already public and cannot itself earn credit.

Krattenthaler's actual published article, DOI10.1007/s11139-021-00514-8, Theorem1 and Sections2/3, gives the classical polynomial-moment/Christoffel determinant bridge under nonvanishing ordinary Hankel determinants. Those nonvanishing hypotheses fail here. Lascoux–Pragacz, actual author PDF bez7, Theorem11, Propositions31/32 and their proofs, gives the Euclidean-remainder/Bezoutian route. This makes a complete classical bridge a serious eligibility objection; no claim of substantive novelty is made merely because of vanishing minors.

## Sustained route 1: all-order truncated monodromy

For a cycle entry (k,v,D) in the public n+1 shifted H-fraction, form the reversed denominator

    a(x)=x^(k+1)D(1/x),  T(x)=[[a(x),-v],[1,0]].

The source denominator-degree bound makes a a polynomial. Multiply these matrices in cycle order, acting on column states. Let M be the product. The public first-order transfer calculation gives M(0)=I for every n; the separate three-term golden cycle is included. This identity, not a conjectural numerical observation, is the only all-n public input used in the following algebraic deduction.

For any d>=0 work in R=Z[x]/(x^(d+1)). Set N=M-I. Since every entry of N is divisible by x, N^(d+1)=0. Commutativity of I with N and the binomial theorem yield, for EVERY integer m>=0,

    M^m = sum_(h=0)^d binom(m,h) N^h  in Mat_2(R).

Consequently each coefficient of x^a, a<=d, in each transferred state is an integer-valued polynomial in m of degree at most a. Multiplication by the fixed prefix of a cycle preserves this property. This is a complete elementary HELPER deduction, already implicit in the public transfer mechanism; it is not a resolution of ConjectureC and is not a separate outcome. The bounded code verifies the full reversal formulas for n1..16 through jet degree8 and vanishing differences through degree6. Finite checks do not replace the all-n identity input.

What this route does NOT show is that EVERY source shifted Hankel minor is a fixed polynomial expression in these jets. In particular, one cannot simply iterate Desnanot–Jacobi by dividing by a determinant: entire normal-index gaps have zero denominators.

## Sustained route 2: complementary minors and a finite kernel

Let H_m=(mu_(i+j))_(i,j<m) be a nonsingular normal-index Hankel matrix for the BASE shift ell0=n+1. All its normal determinants are units by the lower-shift source theorem. Define c(x)=x^m+sum_(i<m)c_i x^i by

    (c_0,...,c_(m-1))^T = -H_m^(-1)(mu_m,...,mu_(2m-1))^T,

and b(x)=sum_(i<m)(H_m^(-1))_(i,m-1)x^i. The finite Hankel/companion displacement identity gives

    (x-y) sum_(i,j<m)(H_m^(-1))_(i,j)x^i y^j
       = c(x)b(y)-b(x)c(y).

This holds without nonvanishing of smaller principal minors; it is the finite Bezoutian form behind the public cofactor proof. It follows by the same selfadjoint companion argument in the actual public `normal_cofactor` proof. Independently checked coefficientwise at all unit normal indices m<=18 for n1,2,3 (5594 coefficient equations).

To represent a desired t-shifted determinant of size j, choose a normal m>=j+ceil(t/2). Let a=floor(t/2), z=ceil(t/2), I={a,...,a+j-1}, J={z,...,z+j-1}. The corresponding H_m minor is exactly Delta_j^(ell0+t). Jacobi's complementary-minor identity gives

    Delta_j^(ell0+t) = (-1)^(sum I+sum J) det(H_m)
                      det((H_m^(-1))_(J^c,I^c)).

Each deleted-index set consists only of a prefix and a suffix. Normal-index gaps are bounded in n, so one may choose m-j bounded in n,t. Thus the remaining inverse minor has bounded size. This identity is exact even when the desired determinant vanishes (1010 finite independent checks).

The kernel formula reduces its low/low entries to finitely many LOW coefficients of c,b. Its high/high entries reduce to finitely many coefficients of the reversed c,b: indeed, with cR=x^m c(1/x) and bR=x^(m-1)b(1/x),

    x^(m-1)y^(m-1)K(1/x,1/y)
       = (y cR(x)bR(y)-x bR(x)cR(y))/(y-x).

For mixed corners use the low-index-first expansion of the same Bezoutian. This identifies exactly the data a proof must control, rather than assuming every ordinary orthogonal polynomial exists.

### Precise unresolved interfaces

A. Identify c,b at ALL normal indices with the source's consecutive H-fraction denominators, including normalization of b and its gap-dependent leading moment, uniformly in n. The public two-shift cofactor theorem alone is insufficient.

B. Prove that both low and reversed-end coefficient windows of these c,b are polynomial on each required cycle class. The truncated reversed transfer proves only one end directly. Forward denominator jets stabilize eventually, but that observation is not an established all-index theorem here. No claim that eventual stabilization implies the literal source conclusion.

C. Assemble the bounded complementary minor, normal determinant sign, normal-size offsets and cycle prefixes with exactly period rho. Finally prove extension from eventual m to EVERY m>=0 and integer-valuedness on all integers. A finite-prefix exception cannot be absorbed into a polynomial unless it agrees with its polynomial continuation.

No complete ordinary source proof or refutation exists in this lane; therefore no PROOF.md, Lean or discovery nomination.

## Falsifiers and objections

Strongest mathematical falsifier: some high/reversed-end coefficient window has persistent dependence outside the required polynomial cycle law, or a low-size source determinant disagrees with an eventual polynomial continuation. Neither is excluded by the tests. Strongest invalid shortcut: assume nonvanishing of all principal Hankel determinants or divide through a zero normal-index gap.

Strongest eligibility objection: completing A–C may be a routine assembly of the already-public all-n monodromy and classical finite Hankel inversion/Christoffel identities. The new conjecture's date and a clean search do not settle this. A future full proof needs an explicit substantive assessment before Lean investment. Full old unboundedness is excluded as public; it is not repackaged as a fresh discovery.

## Exact validation and limits

`sh run.sh` reproduces sequential, bounded, stdlib-only checks. 16 cycle monodromies; Hankel determinants j0..80 for n1 at shifts3..7 and j0..72 for n2 at shifts4..8 (770 exact determinants total). Bareiss uses exact division assertions. Fifteen small determinants are independently recomputed by permutation expansion. 134 known-period identities and six known public linear-subsequence values agree. Finite difference tables are explicitly diagnostic, do not set a universal degree bound, and are not proof. The field `first_zero_difference_order` is an empirical finite-table property; null means insufficient samples, not failure of the conjecture.

Initial IndexError for the zero-th matrix power's short coefficient list and an exec-import __file__ error are retained verbatim in failure receipts. Both repaired without changing caps. Every Python subprocess used the copied capped runner: AS512MiB, sampled process-groupRSS512MiB,CPU210s,wall230s,40ms sampling,BLAS1. Unsampled transients are not ruled out.

Freshness HOLD: inherited GitHubAPI403 was not retried or evaded. No usable reset header was available in the inspected r57/r60/r63 provenance. Latest observed commit is NOT claimed current HEAD. Exact immutable raw body fetches are targeted content reads, not a freshness refresh. No complete latest actual Lean-tree delta, exhaustive registry search or worldwide novelty clearance is asserted. Root alone decides acceptance; counts remain7additional/37total, lanecredit0.

Additional closest-body check: Krattenthaler Section8 Corollary9 and proof explicitly assumes eventually constant ordinary three-term recurrence coefficients and derives a fixed linear recurrence by tensor products; repeated characteristic roots yield polynomial factors. That does not directly supply metallic normal-gap normalization, exact rho or the all-initial-index clause. It strengthens the routine-general-bridge objection, rather than clearing it. Its singular discussion in Section7 treats repeated roots in the Christoffel deformation, not automatically all vanishing base Hankel minors.

Validation correction retained in failures.md: the golden full transfer was authenticated against actual UnboundedGolden.lean before finalization; the dual-number word alone had omitted its quadratic term. Final check uses k=1,D=1+x-x^2 for the exceptional third state and has correct cycle degree weight4. Earlier diagnostic is preserved and superseded.

Integer-valuedness is not an additional deep gap once exact polynomiality for all nonnegative m is proved: the Newton expansion has integer coefficients Delta^a Q(0), and binom(X,a) is integer-valued on every integer, including negative ones. InterfaceC therefore reduces to exact period and inclusion of the finite initial segment.
