# Constraints on a replacement operation

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

These are supporting deductions with expressly stated hypotheses. They do
not refute FT2. They clarify what the successful replacement would need.

## 1. Noninvertibility on self-Hom must kill the degree-minus-one line

Let E be a finite-dimensional symmetric k-algebra, let X be a nonprojective
module with stable End_E(X)=k, and let L be a finite E-E-bimodule projective
on both sides. Suppose LX is stably isomorphic to X; fix such an isomorphism.
The exact projective-preserving tensor functor induces a unital graded
algebra endomorphism phi of H^a=stable Hom_E(X,X[a]), in all integer degrees.
The isomorphisms comparing shifts are the natural ones from evaluating
projective presentations. In particular, phi preserves shifted composition.

Symmetric duality gives dim H^{-1}=1 and perfect pairings
H^a times H^{-a-1}->H^{-1}. If phi is NONZERO on H^{-1}, it is injective
in EVERY degree. Indeed, if 0!=f in H^a, choose g in H^{-a-1} whose shifted
composite with f is a nonzero element of H^{-1}. Applying phi gives a
nonzero composite. Hence phi(f)!=0. Each H^a is finite-dimensional, so
phi is an isomorphism on each degree, and is a graded algebra automorphism.
This proof uses the composition pairing, not an assumption that arbitrary
exact functors respect a chosen trace form.

Thus an actual noninvertible self-Hom action fixing this stable brick
necessarily kills H^{-1}. This does not show it is unrealizable, nor that
all such functors are equivalences. It imposes an extra negative-degree
condition on a zero/identity construction. The cross-algebra restrictions
in restriction-checkpoint.md really do kill H_E^{-1}; their targets have
different graded dimensions, and the cone calculation shows the resulting
negative groups rather than assuming the generic negative twist formula.
The pairing antecedent is Linckelmann Section 2, especially (2.3),(2.7),(2.8),
and stipulated h:duality. The elementary consequence here is not nominated
as a new-to-literature theorem.

## 2. The simplest local realization cannot be noninvertible

Suppose in addition E is local with residue E/rad E=k, X=k, and LX is
ACTUALLY isomorphic to k as a module, with no projective summands. Since
L_E is finite projective over a local algebra, it is free, say E^r.
Then dim_k(L tensor_E k)=r, hence r=1. Its dimension is dim E; left
projectivity similarly makes it free of left rank one. Identify its left
structure with E. Its right structure is a unital endomorphism sigma:E->E,
so L=E_sigma. Right freeness makes the right action faithful. If sigma(a)=0,
then L a=0; faithfulness implies a=0. Thus sigma is injective and, by finite
dimension, an automorphism. Its tensor functor is an equivalence.

This rules out the ACTUAL-simple-fixed, local, rank-one method only. A stable
isomorphism LX~X with projective summands does not force r=1. The pinned
starting E has multiple simples, so this is not a no-go for its arbitrary
side-projective replacements. The cross-algebra restriction method avoids
the hypotheses, but pays for that freedom with the comparison mismatch.

## 3. Killing central operators is not killing all self-Ext

Let A be finite-dimensional self-injective, S=A/rad A, and M finite.
Let H be a nonnegatively graded algebra of central cohomological operators,
with finite-dimensional H^0. Suppose H acts on Ext_A^*(M,S) through the
characteristic map H->Ext_A^*(M,M). If Ext_A^{>0}(M,M)=0, every positive
operator acts as zero. If Ext_A^*(M,S) were finitely generated over H,
it would therefore be finite-dimensional over k: its finite generators
span over the finite-dimensional ring H/H^{>0}=H^0.

Take a minimal projective resolution P of M. Its differentials land in the
radical of their targets, so applying Hom_A(-,S) gives zero differentials.
Every nonzero finite projective has a simple quotient and hence nonzero
Hom into S. Finite-dimensional total Ext_A^*(M,S) therefore forces P_n=0
for all large n. Thus M has finite projective dimension. Over a
self-injective algebra a finite projective resolution splits backwards
from its last nonzero syzygy, making M projective. Contradiction.

Any FT2 witness must consequently fail this particular finite-generation
hypothesis. Polynomial self-Ext of ONE starting module alone does not imply
finite generation over Hochschild operators for all modules. Nor does
finite field imply that hypothesis. This is a direct proof of the relevant
operation in EHSST Proposition 1.1/Corollary 1.3; that antecedent was read
before drawing the conclusion. It is not a universal FT2 negation.

## 4. Actual Hochschild pushout bimodules do not supply a fixed object for free

For eta in HH^d(A), d>0, represented by Omega_{A^e}^d A->A, the EHSST
Definition 2.1 pushout gives

    0->A->M_eta->Omega_{A^e}^{d-1}A->0.

The syzygies of A over A^e are projective separately on both sides:
start with A and split each resolution sequence on each side. Thus
M_eta is finite and side-projective as well. Evaluation is exact, and its
stable triangle is

    X -> M_eta X -> X[1-d] --eta_X[1-d]--> X[1].

It follows by applying stable Hom(X,-) that

  0 -> coker(eta_X:H^{a-d}->H^a)
    -> stable Hom(X,M_eta X[a])
    -> ker(eta_X:H^{a+1-d}->H^{a+1}) -> 0.

Here H^a=stable Hom(X,X[a]); the class must ACTUALLY lift to Hochschild
cohomology, not merely be a Yoneda generator. This exact formula and the
triangle follow directly from the pushout and shifted composition.

For example, conditionally suppose H^{>=0}=k[z_1,z_2], both generators in
one degree d, and eta_X=z_1 with an actual Hochschild lift. At a=dm with
m>=1, multiplication from H^{a-d} is injective of ranks m and m+1,
so the cokernel line survives, while the other kernel is zero in high
degrees (for d=1 it is injective between polynomial pieces; for d>1 its
source vanishes). Thus the evaluated Hom has dimension 1 rather than m+1.
It is not stably X. Cutting by a second regular operator reduces the
mixed-Hom profile further; no assertion about the resulting object's own
self-Ext follows from this mixed-Hom calculation alone.

If eta_X=0, the evaluated triangle splits instead, giving
M_eta X~X direct-sum X[1-d], as in EHSST Proposition 2.2. This has an extra
nonzero stable summand for nonprojective X, so it too is not automatically
X. Under finite-generation hypotheses killing enough operators forces
finite projective dimension, as Section 3 explains; it does not preserve
the nonprojective all-degree witness needed in FT2.

These distinctions prevent mistaking an actual support-cutting bimodule
for a side-projective functor fixing X and acting by a prescribed
noninvertible endomorphism of its self-Hom algebra. Neither EHSST nor the
present calculation excludes a different realization outside these hypotheses.
