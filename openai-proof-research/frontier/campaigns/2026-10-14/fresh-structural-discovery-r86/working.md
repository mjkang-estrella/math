# r86 — source240 no-maximal-model completion attempt

Author work, not independent review. No candidate or contribution verdict. The frozen full target is unresolved; no weaker assertion is nominated.

## Actual source interface

The CH companion constructs K with LS(K)=aleph_0, two endpoint models at H=beth_(omega_2), and categoricity above Lambda=beth_((2^aleph_1)^+). The endpoint models differ in cardinality of the named base order B: countable versus aleph_1. Its Proposition cat:bounded bounds |I|<Lambda whenever B is uncountable. The size formula is |M|=max(|I|,|B|,aleph_0); B has size at most aleph_1. The conclusion explicitly proves failure of joint embedding and amalgamation over a countable model. These are stipulated source facts, not findings here.

The actual color mechanism uses countably many rows, finite-support row translations over B, finite-support column translations over omega, and colors in 2^omega/=*. One tuple's row changes affect only countably many columns. A strong extension requires every new column to pass all old tuple tests, without exceptions. This exact condition controls directed unions. Countable downward closures collect tuple-dependent bad sets and the finite supports of requested elements; convex hulls in the locally countable order remain countable.

## Concrete obstruction to changing only the strong relation

General lemma. Suppose an AEC L has no maximal models. Every M in L has extensions of arbitrarily large cardinality. For any infinite cardinal theta, recursively take proper strong extensions along theta^+ stages, renaming so they are inclusions. At limits use the AEC union axiom. Picking one new element at each successor gives a model of size at least theta^+. Hence a preserved invariant that confines every extension of M to cardinalities below a fixed bound rules out no maximal models.

Apply this to the source's uncountable-base endpoint model. Any injective language embedding preserves the named uncountable B. All source objects with that property have size <Lambda. Thus no alternative AEC strong relation on the SAME source objects, still consisting of language embeddings and having unions, can eliminate maximal models while retaining that endpoint object. This excludes an operation, not the frozen target.

More generally, eventual categoricity plus no maximal models implies joint embedding: extend any two models to one common cardinal in the categorical tail, identify the extensions by an isomorphism, and compose. The source's two incompatible sectors cannot remain incompatible in a successful completion.

## Padding and reduct attempts

Adjoin an unrestricted disjoint pure-set sort P to each source object and let P grow. This removes maximal models but destroys categoricity at every sufficiently large cardinal: pad each of the two endpoint objects to the same arbitrary large size. Their named B sorts still have different cardinalities, so the expansions are not isomorphic. Fixing the P size as the overall size does not help. This is an explicit failure of this construction, not impossibility of any completion.

Forgetting only the name of B does not erase the invariant if the base projections of column fibers and finite-support incidence remain: their ranges recover B. Erasing those operations instead erases the source's color/strong-extension mechanism, and requires a replacement proof.

Relaxing local countability while keeping convex strong embeddings cannot preserve LS=aleph_0. Given two base points a<c, a countable strong submodel containing them must contain their entire ambient interval by convexity, so that interval is countable. Dropping convexity while retaining local countability permits chains that accumulate uncountably many points between two fixed endpoints, violating union closure.

## A more concrete alternative: variable column-translation groups

A potentially meaningful completion would replace the fixed group [omega]^{<omega} by intermediate subgroups G between that group and 2^omega. At G=2^omega, a column translation can absorb an arbitrary row bit sequence, so the matrix obstruction disappears. This is precisely the operation needed to let an exceptional source model enter a categorical ambient class, instead of merely padding it.

But three interfaces are unpaid:

1. Source colors modulo finite changes cease to be invariant under translations by an infinite-support element of G. Replacing colors by 2^omega/G changes the available coding space, which can be finite for a proper G. The source countable extensional diagrams cannot simply be recoded uniformly in every such quotient.
2. The rule 'all tests are required while G is proper, and waived once G=2^omega' is not a continuity argument. A chain of proper subgroups can have union 2^omega, and countable downward submodels of a full-group model normally have proper G. AEC union/coherence and downward closure must all be proved for the same rule.
3. Enlarging G does not by itself make base sorts of different cardinalities isomorphic. A canonical high-cardinality base and compatible size control must be supplied without forcing uncountable closures of one generator.

One proposed repair ('one infinite-support translator triggers the full group') immediately violates LS=aleph_0 if the semantic rules require every subgroup to be full as soon as it contains that translator: every submodel containing it then has at least continuum many group elements. Another proposed repair ('growth of G forces cardinal growth of B') is not coherent merely as a cardinal inequality: an intermediate induced substructure may contain the new group element but not the required size of B. Actual closure functions or witnesses would have to enforce this locally.

## What the source bound does and does not need

The proof of cat:bounded can be applied after restricting the profiles to ANY aleph_1-sized subset of an uncountable B. Its palette bound is then at most (2^omega)^(aleph_1)=2^(aleph_1), and the union of the countably many selected tuple-exception sets still leaves a point. Thus the proof's global |B|<=aleph_1 hypothesis is not essential to this particular bound on I. This observation does not yield the target: if arbitrary B is allowed, models with small I and huge B reintroduce noncategorical large models. An injective coding B->I could bound total size, but still leaves the preserved uncountable-B obstruction until the variable-G operation is paid.

No completed variable-G class, common categorical extension, or proof of the frozen target has been obtained. The positive source theorem supplies only eventual categoricity with an unspecified threshold; it cannot supply the prescribed endpoint counterexample with new structural assumptions.

## Fixed countable-sector obstruction to the variable-group completion

Here is a stronger obstruction than the preceding informal concerns. Suppose an attempted AEC L has LS(L)=aleph_0 and a distinguished group sort G whose elements are injectively coded by their omega-many named bit coordinates. Let G0 be a fixed countable set of such codes. Consider the full class L0 of models in L for which the codes realized by G are exactly G0, with the inherited strong relation. Assume L contains an endpoint model in this sector.

Then L0 is itself an AEC with LS(L0)=aleph_0. Isomorphism invariance and coherence are inherited. In any chain of models of L0, embeddings fix each bit code, and the injective coding prevents additional copies. Thus the union still realizes exactly G0, and all inherited union and smoothness clauses hold. For downward closure of a requested set A inside M in L0, apply the LS axiom of L to A together with the whole countable G-sort of M. The resulting submodel has size at most |A|+aleph_0 and realizes exactly G0, since it contains that sort and is a submodel of M. Thus it belongs to L0.

The standard existence Hanf bound, explicitly stated in the source240 CH introduction, now applies: a model in L0 of size H=beth_((2^aleph_0)^+) implies arbitrarily large models in L0. Consequently no such completion can force G=2^omega in every sufficiently large model if its source endpoint keeps the original countable group G0=[omega]^{<omega}. This is not a claim that every completion has a canonically coded G-sort, and not a refutation of the frozen target. It closes precisely this proposed absorbing-group selection mechanism.

The same argument rules out a canonical increasing countable filtration G_alpha (alpha<omega_1) as the sole route to a full-group categorical tail: the original fixed G0 sector cannot disappear above H while retaining those AEC axioms. This remains true even if transitions between filtration levels are carefully arranged; the problem is the chain-closed, LS-closed sector, not merely a missing transition formula.
