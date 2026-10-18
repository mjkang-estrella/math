# Family 121: unknown rotation remains an unpaid interface

Author: Myeongjin Kang. Original prose CC BY 4.0. Author-side discovery, not an independent review. No target is frozen and no theorem is nominated.

## Provisional full question

For arbitrary explicit finite integer strings x,y (empty strings included), let CED(x,y)=min_j ED(x,rot_j(y)), with the unique empty rotation convention. Can the pinned source's one uniform randomized algorithm be extended to return a (1+epsilon) estimate with probability at least 2/3 in N^(1+o(1)) worst-case expected logarithmic-word RAM time for every fixed rational epsilon in (0,1), N=|x|+|y|, with all input/numerical/randomness work charged and polynomial-magnitude integer alphabet symbols? The intended question is all strings and all edit scales, not equal-length-only, bounded-distance, periodic, or large-distance scope. This is a provisional question, not an eligibility or novelty claim.

## What the actual source pays

Source121, 01-introduction, 02-geometry and 10-work have been read fully. The source gives (1+epsilon) approximation for one supplied pair. Its connection inequality permits arbitrary child target intervals, and even intervals in a finite used portion of an extended target string. Thus storing yy and asking for a fixed length-|y| window is geometrically compatible. The simultaneous correctness events cover all polynomially many possible interval states.

The work proof is different: 10-work's current-index budget is M ell^O(1) child entries for ONE parent entry. Dependency-path counting starts from the final queried root, yielding M^j 2^o(H) entries at depth j. It does not bound the union of n distinct root states by that same expression. Memoization could help, but no overlap theorem for all rotation requests is established. Simultaneous correctness cannot be substituted for a simultaneous work bound.

The source coarse seed (03-seed, read lines1–240 only) likewise constructs a random table but gives per-first-request expected work. Its shift arrays are restricted to [-k,k] relative to a supplied pair. Merely allowing every global phase expands the shift range without proving the same pruning cost.

## A phase mesh does not yet solve the all-scale question

For y of length n and cyclic phase distance d_circ(i,j), ED(rot_i(y),rot_j(y)) <= 2 d_circ(i,j), by deleting a prefix and reinserting it at the end (or the opposite orientation). The triangle inequality therefore makes f(j)=ED(x,rot_j(y)) 2-Lipschitz on the phase circle.

Given a promised scale k<=CED<=2k and fixed epsilon, a phase mesh of spacing at most epsilon k/8 has a sampled phase with f <= CED+epsilon k/4. Applying an ordinary source approximation with a suitably smaller fixed accuracy yields a (1+epsilon) estimate. The number of calls is O(1+n/(epsilon k)), and on comparable lengths the direct work is N^(2+o(1))/k. This is only an elementary baseline, not a nominee or a lower bound against algorithms inspecting the strings. Finding/handling the scale and all zero cases does not remove its intermediate-scale polynomial loss.

## Exact obstruction to explicit repetition

Let n=2h>=2. Let x=a_0 ... a_(n-1), with all n symbols distinct. Rotate x by h, then replace any k of its positions by distinct new symbols not appearing in x, where 1<=k<n; call the result y. All symbols can be integer labels in [0,2n).

Claim 1: CED(x,y)=k. Any rotation of y contains exactly k symbols absent from x. Each must be introduced by its own insertion or substitution, so any edit alignment costs at least k. Rotating y back by h leaves exactly k substitutions, attaining k.

Claim 2: for every integer t>=1,

    ED(x^t,y^t) >= max(tk,n).

The tk lower bound follows from the new symbols as above. For the n lower bound, view an alignment as a path from (0,0) to (tn,tn), where equal-symbol diagonal edges have cost zero. If it has no equal-symbol diagonal, each of the tn source letters is consumed by a cost-one deletion or unequal diagonal, giving cost >=tn>=n. Otherwise, at any equal-symbol diagonal, the consumed indices i,j satisfy i-j congruent h modulo n: replacement symbols cannot match, and every surviving symbol has exactly the shift h. Consequently the path's integer offset i-j attains absolute value at least h. It begins and ends at zero; its total variation is at least 2h=n. Only horizontal/vertical edges change the offset, by one, and every such edge costs one. Thus the total cost is at least n. This argument applies to all alignments, not just to a selected optimal alignment.

Consequently, a procedure that explicitly repeats both strings t times and uses ED(x^t,y^t)/t as its upper estimate cannot satisfy a (1+epsilon) bound on this family unless

    t >= n/((1+epsilon)k).

An upper ordinary-distance approximation cannot cure that failure. The explicit repeated input has length 2tn=Omega(n^2/k). This remains a polynomial obstruction at intermediate k=n^alpha, 0<alpha<1. It is not only the zero-distance rotational symmetry pathology; CED is exactly the positive k. It does not rule out compressed-string methods, additional corrections, periodic structural analysis, or any cyclic-distance algorithm. No general identity between stable repeated distance and CED is asserted here.

## Primary operation comparison so far

Charalampopoulos et al., STACS2024/arXiv2402.14550v1, Theorems1 and5, solve exact threshold circular pattern matching with O(n+(n/m)k^6) reporting and O(n+(n/m)k^5 log^3 k) decision time. Actual introduction and reduction overview plus Section2 through Lemma12 statement have been read. Their operation is to enumerate a bounded collection of anchors or reduce to approximately periodic strings, then use locked fragments and synchronized periodic submatches. Their output permits substrings of the text; it does not directly certify the full prescribed target endpoints in the provisional CED question. No unsupported exact full-pair reduction is assumed.

Charalampopoulos et al., ESA2026, Theorem2 and technical overview, retain polynomial-in-k amortized time per arriving text symbol and polynomial-in-k space in the online read-only model. They introduce super-locked fragments to handle appending text and overlapping defects. This actual recent theorem does not itself state a near-linear fixed-relative-error bound over all k. The body proof of that theorem has not yet been read.

The paid anchor/periodicity alternatives are promising structural ingredients, but replacing their polynomial defect processing by the source's lazy scalar estimates does not preserve their exact anchor or locked-fragment invariants automatically. No construction closing that replacement has been proved.

## Why the source's shared samples are still local

Actual04-cones lines131–270 and05-bands lines1–330 were then read. Cone locality partitions the two endpoint coordinates into cells of side theta b. One queried state enumerates only the cells in its cost-radius neighborhood; 05-bands shares samples within each WHOLE cell. It does not select one representative over all phases. Along the diagonal family q_j=(j,j+n) in yy, traversing n phases can intersect order n/(theta b) distinct cells (up to the integer discretization). At b of order k this reproduces the uncontrolled n/k scale. This is a count of the local construction's possible cells, not a lower bound on the number actually needed on every input or on all possible batching algorithms. Extending the shared-sample group over the whole phase diagonal would require a new rounded-child-state inventory bound; the current proof uses spatial cell width theta b essentially.

## The actual exact Monge mechanism is not a scalar-oracle interface

ESA2022, Sections3–4 (extracted lines684–850), was read. Its threshold computation maintains an alignment distance matrix D_t inside a width-O(k) diagonal strip. The matrix has an exact permutation representation D_t[i,j]=2P_t^Sigma[i,j]+i-j; the total number of adjacent transpositions is O(k^2). A partially persistent Monge data structure supports the resulting updates and sub-column minima. These are the operations paying the O(nk log^3 k) exact threshold result. Replacing its entries independently by scalar multiplicative estimates does not preserve even the Monge inequality.

Here is an exact contract-level witness. Fix m>=1 and integer R>=2, and use a sufficiently long unary text. For the two starts s=0,1 and ends e=m+R,m+R+1, every selected target interval has length >=m. Its ordinary distance from a^m is e-s-m. Thus the true matrix is

    D = [[R, R+1], [R-1, R]].

The Monge inequality D00+D11<=D01+D10 is an equality. Raise only the top-left entry by a rational delta with 0<delta<=epsilon R, leaving the other three fixed. Every returned entry is still between its true value and (1+epsilon) times its true value, but the Monge inequality fails by delta. Choosing R large also permits delta=1 if integer estimates are desired. This does not assert that the actual source program outputs this table; it proves that its scalar multiplicative contract alone is insufficient for the exact Monge/transposition interface. A joint structured estimator or a new robust data structure would have to be proved.

The locked-fragment operation is similarly more specific than approximate pair distances. Actual STACS2024 Section3, Section4 and Section5 through the start of Algorithm2 (extracted lines725–1030) were read. Lemma20 decomposes a near-periodic string into O(k) locked pieces of total length O(kq), separated by exact powers of a common primitive period. The overlap algorithm explicitly processes pairs of pieces; the non-overlap argument introduces an exact Q^(k+1) sample, finds critical positions, and uses cancellation of equal end letters to transport an optimal alignment. No scalar-estimate-only proof of these identities was found or is claimed. The proof of its final Lemma36 and the complete non-overlap analysis remain unread.

## Disposition

These checks identify a concrete unpaid joint phase/geometry problem but do not provide its solution. The full provisional question remains unresolved. The phase mesh is technical support; the repetition and Monge examples are failures of specified transfers, not counterexamples to cyclic approximation. No narrowed theorem, exponent interpolation, fixed-k restriction, or periodic-only case is offered as a nominee.
