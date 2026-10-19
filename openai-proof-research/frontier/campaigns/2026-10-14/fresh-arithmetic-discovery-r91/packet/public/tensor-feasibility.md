# Tensor nilness and the two simultaneous word streams

This is prefreeze feasibility work, not a theorem nomination. No target was frozen. The question considered is whether one can construct an infinite-dimensional, ordinarily finitely presented, positively graded nonunital associative F2-algebra A for which **every element of A tensor_F2 A is nilpotent**. No bound on the number of summands, their degrees, or their individual nilpotence indices is imposed. Matrix nilness and arbitrary-field scalar extension would be desirable stronger conclusions, but neither is asserted. The full existence question is unresolved here; the discussion below does not prove its negation.

The source247 word algebra is the concrete starting point. Its theorem statements AND operative proof operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The source is not being truth-audited. The source, its residual-finiteness companion, the actual r61 construction and contribution comparison, and the primary interfaces described below were read before this extended note. The calculations of overlap, buffering and a denser palette preceded this note and any possible freeze. There was no freeze at any time.

## Existing constructions were tried first

The source's `fr:basis`, `prop:hierarchy`, `ca:direct`, `ca:cut-reduction`, `ca:automaton`, `ca:all-tests`, `thm:algebra` and `cor:nil-algebra` already give an ordinarily finitely presented, infinite-dimensional, graded nonunital algebra I, with matrix nilness over every characteristic-two field. Its literal words, arbitrary-state rollback, unique cuts, finite token normalization, free packet-permutation orbits and central-variable coefficient extraction are all available operations. Matrix nilness is not a new target.

Actual structural r61 goes further: it tracks coefficient degree and matrix states and uses a permitted variable schedule to obtain one algebra absorbing all coefficient algebras of locally finite GK dimension. Its complete candidate and the actual contribution review were read. The latter's conditional TECHNICAL disposition is historical context, not a verdict assigned by this worker. In particular, its fixed-D estimate already absorbs coefficient exponents below D-1-2kc; commutative and locally finite coefficients have still simpler compatible reductions. The r61 argument does **not** establish finite GK dimension of its constructed A, and expressly does not conclude A tensor A is nil. Substituting B=A in that theorem without the growth hypothesis would be invalid. Merely speeding its schedule is not the operation being sought here.

Smoktunowicz's actual arXiv:1403.2557v1 provides a stronger *tensor* construction: Theorem1.1 constructs a finitely generated, infinite-dimensional graded algebra over an algebraically closed field whose tensor square and opposite tensor square are nil. The inspected Theorem3.1, Theorem6.1, Corollaries6.1–6.2 and Sections7–8 use controlled linear subspaces, codimension-one choices, a tensor ideal containing powers, and the ideal I[D] in one factor. This is not merely separate nilness of the factors. It was therefore tested as the strongest inspected alternative before pursuing paired source packets. The presentation is not asserted finite in those results. No finite-presentation-preserving map from that construction to the source algebra was built.

The exact direct primary versions are [Smoktunowicz v1](https://arxiv.org/pdf/1403.2557v1) and [Durand–Romashchenko–Shen, JCSS author version](https://www.lirmm.fr/~ashen/nafit/2011-jcss.pdf). DRS Section5 explicitly permits variable zoom subject to payload and computation bounds; this operation is credited. Reading limits, including the unread primary helper chains, are recorded separately.

## What a paired cancellation would have to preserve

Write a general tensor element as

    T = sum_gamma c_gamma [v_gamma] tensor [w_gamma],

where both labels are nonempty words and the finite scalars c_gamma lie in F2. Its rth power sums over ONE common sequence of r identifiers. The first and second words may have different lengths; their individual lengths and the number of factors cannot be identified. A matrix version has the same shared sequence with an ordered product of numerical matrices in front.

The source's direct argument does extend without a new algebraic identity if there is a common consecutive packet of identifiers whose first labels lie inside one eligible first-tape run and whose second labels lie inside one eligible second-tape run. Keep the two exteriors and the chunks crossing either endpoint fixed. A permutation of the complete packet preserves both algebra images, both lengths, and the two color-erased words. When the packet selection is invariant under these permutations, all members remain in the same orbit. Distinct colors in the first tape ensure distinct identifiers. The contribution is

    U Alt_m(X_1,...,X_m) V tensor a tensor b.

For numerical d-by-d weights, m>d^2 kills it by the source's exact alternating-multilinear lemma. In the scalar case m>=2 suffices. This is a check of a compatible source operation, not a new contribution. The missing premise is a common invariant packet of adequate size for EVERY surviving term after a controlled number of reductions. Separate eligible runs do not supply it.

## An actual phase issue in the unchanged source

At one level put q=2^h and L=2q+1. A canonical clean block consists of q core cells, q palette cells and one stop. With zero-based positions, the palette residues modulo L are

    P = {q,...,2q-1}.

The shifted set P-q is {0,...,q-1}, disjoint from P. The hierarchy has arbitrarily long nonzero upper words: compose faithful encodings of a nonzero letter from arbitrarily high levels. Encoding such an upper word gives arbitrarily long nonzero strings of canonical clean blocks. Take two long subwords starting q positions apart, with the same length and sufficient room at both ends. They are both nonzero, because a subword of a nonzero word is nonzero by `fr:basis`. At no common coordinate are both letters palette letters.

This is a source-realizable pair, not just an abstract pattern. Thus the unchanged clean-block geometry does not guarantee even one simultaneous palette position for arbitrary two streams. The companion's complete `lem:phases` and `cor:phase-products` were also checked: they propagate phases under subwords and replacements **within one factor**. They do not force two independent tensor factors to have the same phase. Odd phase moduli do not align arbitrary starts.

This does not show a tensor element is nonnilpotent. For example the tensor of the two sums of generators has nil powers by the source theorem, despite its formal expansion containing every such pair. Cancellations can occur outside the proposed common-packet grouping. No method counterexample is promoted to a counterexample to the full question.

## Two-tape compression: finite is not yet quantitatively compatible

One can try to normalize both streams by their source cuts while retaining their correlation. At a fixed level every literal token has length at most kL. A general finite transducer can remember an unfinished literal token on each tape, output its chosen upper normal form on completion, and retain the numerical matrix state. This is a finite construction at a fixed level. The complete source token choices, rather than arbitrary guessed normal forms, are required.

However, the straightforward buffer stores prefixes of words on the declared alphabet Sigma. The unpruned all-prefix construction uses sums of |Sigma|^t states for 0<=t<=kL on each tape. Its logarithmic state bound is of order kL log|Sigma|, hence of order h 2^h with the source alphabet size 2^(ch). This differs from the source's single-tape cost O(h): there it assigns each *whole* literal token a matrix weight and uses only bounded-length **upper** prefixes in the next automaton. It never has to store an unfinished correlated token on a second tape.

For the source successor h'=Dh, the all-prefix cost cannot be paid by the next palette exponent h'. Even a proposed faster successor must fit c h' upper data bits inside the lower core; in the unchanged format c h'<=q. The displayed unpruned buffer bound O(hq) still does not yield a stopping inequality against h'. This compares the explicit sufficient bounds of this particular construction. It is NOT a lower bound for minimal transducer rank, nor proof that a source-specific compression is impossible. Pruning invalid prefixes, factoring the weight matrices, or using additional relations might improve it; no bound achieving the required stopping inequality was proved.

There is an additional interface to settle before claiming a complete transducer reduction: completed tokens can be emitted on one tape before the other. One must account for silent and one-sided transitions, preserve every shared identifier sequence and its weight exactly once, and control output label bounds and end pieces through iteration. No assertion that a generic rational-relation closure theorem pays those quantitative contracts is made here.

The unresolved operation can therefore be stated concretely: a paired weighted-cut reduction with an exact sum identity and a state/label budget small enough for simultaneous packet cancellation, OR another construction that bypasses it while retaining ordinary finite presentation and infinite dimension.

## Denser palettes and linear-ideal alternatives

A feasibility idea was to shorten the core while keeping q palette colors, making palettes occupy almost the whole clean block. The source's tableau has O(T^2) cells with T=2^floor(h/5), so the current q-cell core has spare capacity at a fixed linear successor. If a modified core had length Q=o(q), two clean equal-speed streams would have at least L-2(Q+1) common palette positions per period. This is only the elementary overlap calculation. No modified compiler was proved for arbitrary forged states, no simultaneous packet selector for arbitrary unequal chunk labels was supplied, and the two-tape weight-memory budget remains. A favorable clean overlap count is not a replacement theorem.

The tensor-ideal method was also tested at its actual interface. The primary constructs linear subspaces U_i and imposes linear relations via I[D], while protecting nonzero dimensions with Golod–Shafarevich estimates and codimension-one choices. The source's finite compiler accepts word equalities and zero words. By `fr:basis`, a relation among three distinct surviving word classes is not silently available from that contract. Encoding arbitrary linear subspaces as word equalities would require a separately proved representation and protection argument. DRS variable zoom changes scale; it does not by itself supply this algebraic conversion or finite generation of the primary ideal. No such conversion was constructed here. This is an interface limitation, not a claim that all finite-presentation encodings are impossible.

Finally, the multiplicative word basis gives the elementary diagonal homomorphism [w] -> [w] tensor [w]: zero words and binomial equalities are respected, and different surviving classes have independent diagonal tensors. Its image is a copy of the nil algebra. The tensors appearing in a general T above need not lie in this image. Similarly, finite-degree quotients detect fixed nonzero coefficients but do not supply a common nilpotence index over all truncations. Neither diagonal tensors nor finite quotients repair the full question.

## Disposition

No full tensor-nil finite presentation was obtained, and no target was frozen. The surviving mathematical work is the exact comparison of the two-stream problem with the already available one-stream and tensor-ideal operations. The paired reduction budget, invariant joint packet selection and finite-presentation-compatible linear encoding remain unproved. No restricted diagonal, finite-degree, coefficient-growth, local overlap or matrix-only substitute is nominated. This archive assigns no correctness or contribution gate and makes no worldwide priority or exhaustion claim.
