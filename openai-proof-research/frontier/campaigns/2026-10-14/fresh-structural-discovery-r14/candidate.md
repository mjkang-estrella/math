# Finite-field self-orthogonality: fresh structural round 14

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party sources remain
private and retain their original rights.

**UNRESOLVED_FULL_FT2.** Family 199 supplies the distinct source family.
No proof or counterexample to the frozen target was obtained. There is no
independent proof/contribution PASS, substantial nomination, manuscript,
Lean package, publication, or count increase. The campaign remains 4/10.
The finite-window deduction below is explicitly supporting research.

## The exact unchanged target and stipulated inputs

FT2 asserts that there exist positive integers a,m, an associative unital
F_2-algebra A of dimension a, and a unital left A-module M of dimension m,
such that A is symmetric, M is nonprojective, and

                        Ext_A^i(M,M)=0 for EVERY i>=1.

Symmetric means A is isomorphic to Hom_{F_2}(A,F_2) as an A-A-bimodule.
There is no restriction on dimension, radical length, number of simples,
complexity or presentation. One fixed finite A,M must work in all degrees.
To refute FT2 one must establish a positive self-extension for EVERY
finite-dimensional symmetric F_2-algebra and every finite-dimensional
nonprojective module. No subclass obstruction is such a refutation.
`original-scope.md` was frozen before sustained proof work, SHA256
`1b6e3b67f7a9ff756eb507a3c8f332048de2cbab0eae5e62b9fe8cd4e0a7e80a`.

Accept openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
*A counterexample to Tachikawa's second conjecture*, `introduction.tex`,
`thm:main`, supplies a finite symmetric algebra and a nonprojective
self-orthogonal module over K=F_2(q,H_1,H_2), with three algebraically
independent parameters. The companion *An explicit counterexample to the
Auslander--Reiten conjecture*, `01-introduction.tex`, `thm:main`, supplies
a finite split eight-simple algebra and nonprojective Gorenstein-projective
module over K with both required positive Ext vanishings. Both allow
field EXTENSIONS of K. Neither gives specialization to a finite field;
the symmetric paper explicitly distinguishes its closure from F_2bar.
Their truth is stipulated, not audited.

The additional operation selected is finite-field replacement of
infinite-order homological parameter separation, preserving
nonprojectivity and ALL positive vanishings. Merely extending scalars,
forgetting a transcendental field structure (which gives infinite
F_2-dimension), or proving a different finite window does not pay it.
The selection was compared before freezing with the actual Schulz,
Erdmann, and Enomoto--Marczinzik operations below.

## What a finite-order specialization does to the actual starting complex

The symmetric source's `algebra.tex`, `a:resolution`, uses R_0=Cf,
R_j=Ce for j>=1, d_1=rho_u and d_j=rho_{ell_{j-2}} for j>=2,
where ell_i=x+q^i y. The table gives

 rho_u(e,x,y,z,t,j)=(u,v,v,0,(1+q)n,0),
 rho_{ell_i}(e,x,y,z,t,j)=(ell_i,q^{i+1}z,z,0,(1+q^{i+2})j,0).

These formulas can be evaluated at nonzero q in any characteristic-two
field. They remain a complex because ell_0 u=0 and
ell_i ell_{i-1}=0. If q has order L>1, then L is odd and >=3.
The ranks are 3 for d_1 and 3-1_{L divides j} for d_j, j>=2.
Therefore

       dim H_j(R)=1_{L divides j}+1_{L divides j+1}, j>=1.

This follows by subtracting the ranks of the outgoing and incoming maps
from dim Ce=6. The augmentation is exact in degree zero. The first
failure is H_{L-1}=k[j], followed by H_L=k[t]; the vectors named here
are table basis vectors, not indices. At q=1 the augmented H_0 has
dimension one and every positive H_j has dimension two. Thus no nonzero
finite-field specialization retains this displayed infinite resolution.
One must repair the new homology before claiming its polynomial Ext
calculation survives. This is a method failure, not a counterexample to
FT2 or an audit of the generic source theorem.

## Why changing just the twist parameters or matrices also fails

Grant, conditionally, the polynomial stable self-Hom profile of the
source's `stable.tex`, `e:all-degrees`, over a finite field k. Its positive
degree 3m component is k[tau_1,tau_2]_m, of dimension m+1.
The source's `e:twists` and `triangular.tex`, `t:projected-delta`, give
the comparison matrix with rows (H_1^{-m},1),(H_2^{-m},1).
If H_1/H_2 has order L, these rows coincide at m=L. Their kernel
and cokernel each have dimension L+1. The source's exact cone identity

 0 -> coker Delta^{a-1} -> H^a End(P_Z) -> ker Delta^a -> 0

then forces positive self-Ext in degrees 3L and 3L+1, PROVIDED the
fiber/profile/complete-resolution hypotheses still hold. The preceding
starting-complex failure prevents asserting those hypotheses for a naive
actual specialization. These are two separate obstructions.

There is a stronger obstruction to automorphism replacements within the
same polynomial mechanism. Any graded automorphisms of k[x,y], with
both generators in the same positive degree, generate a finite subgroup
Gamma of GL_2(k). The orbit product u=product_{gamma in Gamma}gamma(x)
is a nonzero homogeneous invariant, since the polynomial ring is a
commutative domain and Gamma permutes its factors. Powers of u give
arbitrarily high common invariants. If branch projections remain injective
in high degrees as in the source's sparse fiber, then

              p Delta(u,u)=(phi_1(u)+u,phi_2(u)+u)=0

implies Delta(u,u)=0. The same cone identity supplies nonzero positive
self-Ext. Additional finitely many graded twists have a common orbit
product as well. This uses a classical invariant operation; it is not a
new invariant-theory theorem or an impossibility claim about other
Ext algebras, fibers, or functors.

A noninvertible scalar action might evade this. The attempted realization
H=0 uses h_0:T=C lt DC -> T, (a,phi)->(a,0), and U_0=E_{h_0 tensor h_0}.
It loses right projectivity. Indeed K_0=DC tensor DC is killed by this
right action. For every primitive vertex idempotent p=p_1 tensor p_2,
pK_0=(p_1 DC) tensor(p_2 DC)!=0: choose a functional nonzero on each
p_i and evaluate p_i phi at 1. Every nonzero finite projective right
E-module is a sum of such pE, and thus is not annihilated by K_0.
So U_0 cannot be projective. Since E is symmetric, a finite projective
resolution would split backwards and make U_0 projective. Thus a bounded
projective replacement cannot restore the exact tensor functor needed
by the conversion. This does not exclude a DIFFERENT side-projective
functor with the required noninvertible action. None was constructed.
`specialization-checkpoint.md` gives the full statements and limits.

## A complete supporting deduction: every finite window descends

For every r>=1 the stipulated symmetric example can be specialized to
a finite field k_r, with its original dimensions over k_r, preserving
nonprojectivity and Ext^i=0 for 1<=i<=r. Here is the finite argument.
Choose its multiplication/action/symmetrizing coefficients, a finite free
resolution prefix through degree r+1, and the induced Hom differentials.
All are over a localization of F_2[q,H_1,H_2]. For each of the finitely
many relevant matrices, invert a nonzero minor of its generic rank.
Larger minors vanish identically. Differential identities and preserved
rank sums prove exactness of the prefix and of its Hom complex in the
required degrees. Invert the symmetrizing determinant as well.

To preserve NONprojectivity, use the free surjection A^m->M sending
basis generators to a basis of M. An A-linear section solving pi s=id
would be a solution of a finite inhomogeneous linear system. Its generic
coefficient and augmented ranks differ. Inverting minors preserving this
rank gap ensures every fiber remains nonsplit. Thus every fiber in one
nonempty open set has all the asserted finite-window properties.
A nonzero polynomial has a nonzero value somewhere over the infinite
field F_2bar; the finitely many coordinates of that point lie in one
finite subfield k_r. This gives the asserted fiber.

For k_r/F_2 of degree e_r, forgetting the named field structure gives
an F_2-algebra of dimension e_r a and a module of dimension e_r m.
It remains symmetric via Tr_{k_r/F_2} composed with its symmetrizing
functional. Nondegeneracy follows from the nonzero finite-field trace
and multiplication by a nonzero scalar. Projectivity and the additive
Ext groups depend on the underlying ring, which has not changed.
Thus arbitrary finite windows over exactly F_2 are proved.

This does NOT prove FT2: e_r may grow. With UNIFORM bounds on the two
F_2-dimensions, only finitely many algebra/module tables exist. If each
had a first positive self-extension, their maximum first degree would
contradict sufficiently long finite-window vanishing. Hence uniform
bounds would prove FT2; no such bounds were found. Infinite intersections
of the nonempty opens q!=0, q^j!=1 (j<=r) illustrate why a generic
witness need not yield an F_2bar point. `finite-window-checkpoint.md`
contains all rank, base-change and quantifier details. These standard
operations are not nominated as a substantial result.

FT2 is equivalently existence of such a witness over F_2bar: finite
structure constants descend to a finite subfield, all-degree Ext
vanishing descends by faithful field extension, and the trace argument
returns to F_2. Conversely field extension preserves symmetry, Ext and
the nonsplitting rank gap. This closure is distinct from the source's
algebraic closure of a rational-function field.

## Necessary syzygy growth and the exact remaining operation

Any full finite-field witness would have minimal syzygy dimensions
TENDING TO INFINITY. Over a self-injective algebra Omega is invertible
in the stable category and Ext^d(M,M)=stable Hom(Omega^d M,M).
A repeat Omega^j M isomorphic to Omega^l M, j<l, would give a nonzero
stable period and hence nonzero Ext^{l-j}. Over a finite field a fixed
finite algebra has only finitely many modules in each bounded dimension:
an a-dimensional algebra action on k^d is described by a matrices of
size d. Thus each dimension bound can occur at only finitely many
syzygy indices. This proves the stated limit, but supplies no
contradiction; FT2 imposes no bound on syzygies. The proof and its
finite-window limitation are in `syzygy-checkpoint.md`.

**Still unpaid:** construct ONE finite symmetric F_2-algebra and ONE
finite nonprojective module with ALL positive self-Ext groups zero,
or prove that no such pair exists. The source construction cannot be
specialized unchanged. An exact functor with a genuinely different
cohomology action, or a uniform-dimensional finite-window construction,
would have to pay additional mathematics. Neither was obtained. No
finite test or integrity check decides this quantifier.

## Primary comparison, continuity, and evidence limits

Schulz (1995), Example 7, gives non-root-of-unity parameter-shifting
syzygies and eventual self-Ext vanishing with a nonzero first group.
Erdmann (2017), Theorem 1.1, classifies eventual-vanishing examples in
its weakly symmetric radical-cube-zero setting by non-root-of-unity
parameters. Neither supplies an all-degree finite-field witness.
Enomoto--Marczinzik (2026), Theorem 1.1, Proposition 3.4 and Theorem 3.5,
use trivial extensions over a FIXED artinian coefficient ring; their
reduction does not lower the field, and its self-injective target is
not automatically symmetric. These are operation-level distinctions,
not a claim that the restricted target is new to literature. The
classical orbit-product, rank specialization, trace and periodicity
arguments above remain technical support. No substantial result emerged.

The current campaign ledger and complete required 59582-byte r2 brief
were read and snapshotted; the latter matches the supplied SHA256
56aac13aa84140897d92c4d5904ae5846fc293464511c6c754e496b4a3065931.
No TFS, Artin, Spin, analytic, crossing, or other excluded target was
continued. The five fixed original source/context files were unchanged in
the final before/after observation. The live ledger gained unrelated
parent updates (LC reviewed as technical and distinct analytic r13 launched),
still at 4/10. Its original snapshot and observed delta are retained;
no future live ledger bytes are a verification dependency. The complete nontruncated catalogue was parsed structurally
(all 13223 entries); catalogue titles and selected family descriptions
were surveyed, not every manuscript semantically read. Actual theorem
and proof reading is enumerated in `source-contracts.md` and
`inputs/reading-records.json`. Authentication is not reading.

No mathematical numerical scan or historical/third-party program ran.
The sole stored executable is the new read-only integrity verifier,
inspected and hash-authenticated before execution. Manifests bind exact
owned input/output membership, sizes, SHA256 and pinned Git blobs. A
detached seal is reported externally. Source before/after receipts are
historical observations; the verifier uses INTERNAL snapshots and does
not bind future mutable ledger/context state. Integrity is not a
mathematical or contribution verdict. All writes stayed in this r14
directory; no nested agents, staging, commits, external messages,
uploads, submission, or publication occurred.
