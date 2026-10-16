# Unchanged full FT2: focused research round 2

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party materials remain
private and retain their original rights.

**UNRESOLVED_FULL_FT2_AFTER_TWO_ATTEMPTS.** No witness and no universal
impossibility proof was obtained. The full target is preserved. No independent
mathematical/contribution PASS, substantial nomination, manuscript, Lean
package, count increase, publication or submission is claimed. Current 4/10
is unchanged. The present supporting work is an all-degree rejection of a
DIFFERENT, genuinely realized finite-field mechanism, together with precise
constraints on a replacement. It is not another scalar specialization scan.

## Exact assertion and authenticated history

FT2 asks for ONE finite-dimensional associative unital symmetric F_2-algebra
A and ONE finite-dimensional nonprojective unital left module M such that
Ext_A^i(M,M)=0 for EVERY i>=1. Symmetry is the A-bimodule isomorphism
A~Hom_{F_2}(A,F_2). There is no restriction on dimension, radical length,
number of simples, complexity, syzygies or presentation. A negation must
rule out EVERY such pair. A finite window or a subclass theorem does neither.

The frozen original-scope.md is byte-identical to r14, SHA256
1b6e3b67f7a9ff756eb507a3c8f332048de2cbab0eae5e62b9fe8cd4e0a7e80a.
Before relying on r14, this round independently authenticated its supplied
seal 88428e36011c09d7920f4ebf36da39511af77f1bd770220d3f0ce49df02ee6d2,
all 49 files, their sizes/hashes, and EXACT inferred directory membership.
The total was 6902898 bytes. No stored verifier was executed.
The fixed history remains at ../fresh-structural-discovery-r14/; its exact
membership is bound in inputs/r14-authentication.json. It was not copied
wholesale. The mutable campaign ledger was snapshotted internally and is
never a future verification dependency.

The stipulated upstream is openai/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Actual introduction thm:main
supplies the generic symmetric witness over F_2(q,H_1,H_2), with independent
parameters, not over the algebraic closure of F_2. Its truth is accepted,
not audited. Seven relevant original Git blobs are recorded precisely in
inputs/pinned-references.json. This round read the complete bimodule and
homological sections, beyond r14's partial reading, as well as the stable,
triangular and transfer operations. Source contracts below distinguish actual
reading from byte authentication.

All earlier limits remain: finite-window descent has no uniform F_2-dimension
bound; finite-order q breaks the displayed starting resolution; the separate
conditional scalar Ext obstruction is not actual specialized Ext; polynomial
orbit invariants only obstruct that template; the named H=0 bimodule loses
right projectivity and cannot be fixed by its bounded projective replacement;
unbounded syzygies are permitted by FT2. None is promoted to a general no-go.

## The different operation pursued

The principal attempt replaces parameter twists by actual subgroup-style
restriction functors. It changes the starting object to one over F_2 whose
minimal syzygy dimensions are 2n+1. This avoids both a moving scalar orbit
and bounded syzygies. Its noninvertible cohomology projections are realized
by finite bimodules free on BOTH sides. The mechanism was carried through
the triangular conversion and ordinary symmetric trivial extension, including
negative complete-Hom calculations; it fails for an exact mathematical reason.

Put k=F_2,

    E=k[x,y]/(x^2,y^2), B=k[u]/(u^2), X=E/(x,y), T=B/(u).

The coefficient-of-xy and coefficient-of-u forms make E and B symmetric.
Let L_x,L_y be the B-E-bimodule E with left u acting by x,y respectively,
and regular right E action. Each is right free of rank one and left free
of rank two. Set F=L_x direct-sum L_y. The exact functors L_i tensor_E -
are the two restrictions, preserve projectives, and send X to T as actual
modules. Their positive cohomology maps are

    k[alpha,beta] -> k[t],
    (alpha,beta) -> (t,0) and (0,t).

Thus noninvertibility is REALIZED. It is a map between DIFFERENT cohomology
algebras. It cannot be silently interpreted as a zero/identity pair of square
maps on the source's original polynomial pieces.

Tensor the rank-one periodic resolutions in x and y to get the minimal
resolution of X with E^{n+1} in degree n. Its syzygy dimensions are exactly
2n+1. All products and positive dimensions follow from tensor comparison:
H_E^{>=0}=k[alpha,beta], with both generators in degree one, whereas
H_B^*=k[t,t^{-1}] in the complete stable category. Symmetric duality gives

    dim H_E^a=a+1 for a>=0, and -a for a<=-1;
    dim H_B^a=1 for EVERY integer a.

Negative restriction is zero. In degree -1 the nonzero socle map
X->rad E, 1->xy, restricts through the B-projective B: for u=x, send
1 in T to u in B and 1 in B to y in rad E. The other restriction is
symmetric. In degree -n-1, multiply by alpha^n or beta^n to reach the
socle line. Restriction becomes multiplication by the invertible Tate
class t^n, so it too must be zero. This checks the negative action instead
of importing a generic twist weight that need not survive modification.

## A complete bridge to conversion, and its actual failure

Form the 14-dimensional triangular algebra

    R=[[E,0],[F,B]].

Use complete resolutions P,Q of X,T and the actual diagonal map
v:T->FX=T^2, 1->(1,1). Complete-resolution comparison lifts v to Q->FP.
The standard projective columns D_0(P),D_1(Q) are exact and totally acyclic:
their Hom complexes into R reduce to Hom_E(P,E), Hom_B(Q,B),
Hom_B(Q,F), and zero. Left B-projectivity of F pays the third exactness;
right E-projectivity pays tensor exactness. Their cone C has finite
projective terms and is totally acyclic.

Its finite degree-zero cokernel Z has upper component X and lower component

    N=(k^2 direct-sum B)/k(1,1,u),

with the evident inclusion FX=k^2->N. Thus dim Z=4. The upper-component
functor sends R-projectives to E-projectives, so Z is nonprojective.
No conjectural fiber lift is used: the map v is ordinary and the requisite
chain lift was justified. A sparse bimodule fiber correction is considered
separately below rather than asserted to exist.

Let K^a=H^a Hom_R(C,Z). The full End complex, retaining products over the
resolution indices, gives

    0 -> coker Delta^{a-1} -> K^a -> ker Delta^a -> 0,
    Delta^a:H_E^a direct-sum H_B^a -> (H_B^a)^2,
    Delta(g,h)=(r_x(g)+h,r_y(g)+h).

This mixed-base identity is independently proved by the column Hom blocks
and the connecting differential; the pinned same-base proposition is not
applied without its hypotheses. In positive degree a the map has rank 2
and domain dimension a+2, so its kernel has dimension a. In degree zero
both kernel and cokernel are lines. In every negative degree the two
restrictions are zero, so Delta(g,h)=(h,h); its kernel dimension is -a
and cokernel dimension one. Consequently the ACTUAL complete groups are

    dim K^a=a for a>=2;
             2 for a=0,1;
             1-a for a<=-1.

Positive self-Ext and all required negative groups survive. This is a
proved all-degree failure, not a numerical scan or a conditional Ext
calculation for the generic source specialized at finite scalars.

The stipulated ordinary trivial-extension argument, independently checked
for this modified input, still constructs A=R lt DR and M=A tensor_R Z.
It supplies the unconditional identity, for every i>0,

    Ext_A^i(M,M)=K^i direct-sum D K^{-i-1}.

Indeed DR tensor_R C=D Hom_R(C,R) termwise, hence is exact by total
acyclicity. Thus A tensor_R C is an exact induced-projective resolution;
its DR-tail is an injective coresolution with the precise index -i-1.
Adjunction then gives the displayed sum. If M were projective, tensoring
its splitting with A->R would make Z projective, a contradiction.

Here dim A=28 and dim M=10 (the checkpoint computes
Hom_R(Z,R) explicitly, of dimension 6). The exact self-Ext dimensions are
5 for i=1 and 2i+2 for EVERY i>=2. This is not an FT2 witness. Its role is
to expose exactly where a real noninvertible functor fails the conversion.
The complete proof is in restriction-checkpoint.md.

For these very restrictions, a side-projective fiber correction whose
mixed stable Hom is bounded in degree cannot help: outside that bounded
range it leaves target dimension 2, but the comparison domain still has
dimension a+2. Kernels therefore survive in arbitrarily high positive
degrees and sufficiently negative degrees. This excludes only this
restriction/sparse-fiber mechanism, not all exact functors or FT2.

## Replacement constraints and primary antecedents

A new useful checkpoint comes from symmetric duality. If an exact tensor
endofunctor fixes a stable brick X (stable End X=k), its action on the
one-dimensional H^{-1} is either zero or forces injectivity on EVERY H^a:
pair a nonzero class with a complementary one into H^{-1}, and apply the
functor. Since each H^a is finite-dimensional, nonzero action on H^{-1}
forces graded automorphisms. Thus a noninvertible self-Hom action fixing
X must KILL that line. This is a necessary constraint, not an impossibility
proof. The local actual-simple-fixed rank-one situation is even more
restrictive: both-side projectivity forces its defining endomorphism to
be an automorphism. Stable fixing with projective summands, nonlocal E,
and different functors remain outside that elementary argument.

The EHSST primary body was inspected at operation level. Its Hochschild
pushout bimodules M_eta ARE side-projective, but their evaluation is a
cone of an ACTUAL Hochschild operator, not an arbitrary prescribed
endomorphism of self-Hom. A regular polynomial operator changes the
evaluated mixed-Hom profile; a zero operator splits off an additional
shifted X. Neither fixes X for free. Under finite-generation of
Ext_A^*(M,A/rad A) over operators acting through Ext_A^*(M,M), all positive
self-Ext vanishing would force finite projective dimension, hence projectivity.
The short proof is supplied. This is the operation in its Corollary 1.3,
not a universal finite-field theorem. Merely having polynomial self-Hom
for ONE source object does not imply that finite-generation hypothesis.

Bergh--Sandoy--Solberg's actual counterexample to a bimodule tensor-product
support formula uses automorphism twists. It does not justify an arbitrary
noninvertible action or a universal support-intersection formula; its
proof, not just its abstract, was read. Linckelmann's duality and composition
interfaces were read for the negative-degree and socle operations.
The finite-field Bohmler--Marczinzik example in arXiv:2608.09701v1,
Theorem 3.1/end of Section 3, explicitly has nonzero Ext^3. Its calculation
is not rerun or proposed as an all-degree input. Exact extents, limitations,
URLs, retained bytes and pinned Git identities are in source-contracts.md
and the input records.

The primary comparison in primary-comparison.md claims no worldwide
novelty. Restriction, tensor resolutions, cone comparisons, Tate duality,
Hochschild operator cuts and the finite-generation obstruction are known
operations. The new work here is a fully paid modified-input calculation
and its failure checkpoint; it is not a substantial result nomination.

## Exact unpaid operation and final limits

Still unpaid is ONE finite-dimensional symmetric F_2-algebra and ONE
finite-dimensional nonprojective module with EVERY positive self-Ext zero,
or a proof of impossibility for EVERY such algebra and module. For a
conversion of the source type, a successful finite-field construction
must supply actual finite side-projective bimodules (or proved substitutes),
ordinary/evaluated lifts and a fiber with the needed full profile, a finite
nonprojective totally acyclic source module, and vanishing BOTH at a>0
and a<=-2. The successful realization of a noninvertible cohomology map
alone does not pay the latter conditions. No uniform-dimensional finite-window
mechanism or different complete witness was found.

A different noncommutative or infinitely generated self-Hom algebra with a
finite-order action was considered conceptually, but no actual algebra/module,
full profile, lift or conversion was supplied. It is not asserted as a new
route or a conditional result. No assertion about all such cohomology
algebras follows from r14's commutative orbit-product argument.

All writes are confined to this r2 directory. No nested agents, staging,
commits, external messages, uploads, submission, publication, manuscript or
Lean package occurred. Analytic r13 and the crossing audit were not touched.
No mathematical program or historical/third-party research code ran. The
only new stored executable is the read-only integrity verifier, inspected
and hash-authenticated before execution. The final manifests specify exact
owned membership, sizes/SHA256 and source identities; the detached seal is
reported externally. Unchanged-source receipts are historical observations,
not mutable future-state dependencies. Integrity is not mathematical or
contribution acceptance.
