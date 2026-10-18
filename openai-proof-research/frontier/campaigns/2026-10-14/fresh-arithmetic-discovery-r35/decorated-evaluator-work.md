# Semantic decorations: active proof development

This is author-side work toward frozen T250P, not a completed candidate or independent verdict. The source's monoids are denoted K,H,T; its normalizer is f and its raw embedding is c. The fixed code length will be D≥16. All source truth is stipulated.

## Why literal replacement was invalid, and the exact repair

Every raw singleton is fixed by the K evaluator. Thus raw(w) cannot in general be substituted for c([w])=raw(f(w)). For example, a nonempty T-code for the identity reduces to the empty H word, but its raw singleton is distinct in K from raw(empty). The source's raw-product identity nevertheless gives

    raw(w) raw(empty) = raw(f(w)) = c([w]).

This is an equality in K, hence remains valid in arbitrary contexts. Our semantic atoms always mean c([w]); they never mean the unnormalized raw singleton. A standalone native raw singleton remains a separate output type.

## Recursive input syntax

A K decoration is a finite concatenation of native K presentation letters and atoms c(h), where h is an H decoration. An H decoration is a finite concatenation of native Σ letters, T-code atoms κ(k,p), and G-code atoms encoding an element of the source HNN input group. Here k is a K decoration and p is a literal word on the fixed partial-affine monoid generators. A T-code atom means the canonical code of (k,p), or ζ if k=Ω; identity code atoms mean the empty word. Group-code atoms mean their canonical group code. Every tree is finite and all group/P words at its leaves are explicit. This syntax represents ordinary monoid elements, not new algebraic generators.

The two types of opaque H code atoms use disjoint b,a,c alphabets. None contains selector markers d,l,r,h or ζ unless the T value is zero. A nonempty code consists of complete fixed-length blocks b followed by D−1 a/c symbols. This self-synchronization is crucial.

## K normalization without expanding semantic atoms

The source quiver forces every complete c(h) atom to be a whole sector: it starts with α, has its Q head and clean payload, and ends with ω. Any compatible neighboring factor meets it at an ωα cut. Consequently a native validator/machine sector never contains any of its hidden payload. Native sectors are normalized by the source finite-component algorithm. A sector with k native cells has at most (k+1)h c^k configurations. Weak connectivity can be tested in polynomial space by enumerating configurations and their forward trajectories: a finite functional graph has one eventual cycle or sink in each weak component, so two vertices are weakly connected exactly when their forward orbits intersect. Counters and configurations take O(k) space. Entry/success searches and lexicographic minimum searches need no stored component.

After native preprocessing, a maximal run of at least two full raw sectors is replaced by the single semantic atom c(h1…ht), with a native payload used literally and an existing semantic payload used as an H decoration. A singleton native raw(w) is left literal, as required by the source. A singleton c(h) remains semantic. Native preprocessing adds no unbounded payload: the source grade bound is at most twice native input length.

To compare two final K outputs, compare their sector patterns and native letters. Two semantic raw sectors are compared by H equality. A semantic raw sector c(h) equals a native raw(w) exactly when w is irreducible for the H rules and [w]=[h] in H. Two native raw sectors are compared literally. Zero is handled separately. No hidden raw payload is fed to a native machine search.

## H normalization with code values, not code strings

Maintain native letters and semantic code atoms. Repeatedly:

1. Detect T-zero atoms and native ζ; apply the source absorbing-zero rule.
2. Remove identity atoms. Parse every complete valid native code block, replacing maximal valid runs by code atoms. Combine adjacent atoms of the same code type by multiplying their underlying T/group values. Reparse if an empty atom disappears. No valid code straddles a nonempty atom boundary except concatenation of complete blocks: every code begins at b and its remaining D−1 symbols contain no b.
3. Apply a selected selector, when present, replacing its entire interval by empty or ζ. Its marker runs are native. It cannot start or end inside a nonzero code atom. Its middle is compared with the selected literal tuple member by matching native letters and comparing whole code runs to the corresponding literal code runs.

No code atom is expanded, even when its canonical representative happens to be short. Matching a selected tuple member is legitimate because that member has been checked irreducible, so its literal code subwords are least representatives. Equality of their T values therefore gives equality of the literal canonical code strings. Final normalized outputs have unique native fragments and maximal nonempty code runs; compare those runs by their T/group values.

Each rewrite deletes native letters, removes an atom, or combines atoms. Replacing native code blocks by atoms consumes at least D native letters per decoded generator. No selector introduces new markers or new native words. Thus the number of structural changes is bounded by the initial native-letter and atom count; comparisons may take much longer but do not store all their search states.

## Selector eligibility and literal irreducibility

Choose the source's tuple enumeration by length then lexicographic order on an explicit delimiter encoding of finite ordered tuples of distinct words avoiding ζ. Singletons of lengths ≤j show that the first j tuples have encoding length O(j). Choose N_j minimally subject to the source inequalities; compute only until a given native budget is exceeded, using capped integer arithmetic. No tested monoid classes are used in choosing N_j.

A potential selector contains 2N_j+2 native marker letters. Every tuple member at stage j has length <N_j. Eligibility requires each member to be irreducible under the static and earlier selected rules. Test one member at a time. Static code irreducibility is decided by searching all decoded words no greater than the current one in shortlex and comparing T/group values. Earlier selector tests recurse to words of length <N_i. Later selectors cannot fit in a member of the j-th tuple, since their marker lengths exceed its length. Literal irreducibility and selected-rule eligibility therefore admit the same bounded recursive evaluation.

## Size invariant to complete and audit

Weight native K letters by 2, native H letters by 1, and charge a fixed positive overhead to each c or κ wrapper and each literal P/group leaf. A K-to-H raw-run query spends native grade at most 2 per K letter and deletes raw-boundary/wrapper overhead. An H-to-K code-value query deletes κ overhead. A literal static minimum comparison uses two decoded words, of total K weight at most 4|v| versus D|v| code letters. D≥16 leaves room for boundary constants. Selector matching can add a literal comparison word of length <N_j, but the two removed native marker runs already contribute 2N_j+2. Eligibility calls have literal input length <N_j while their parent contains those same marker runs. No short representative is materialized, so this avoids the previously feared repeated squaring of decorated size.

The preceding paragraph records the initial budget proposal. A sharper convention avoids charging native normalization by a multiplicative factor: give a native K letter its source grade, except that grade-zero workspace and Ω have weight one. Thus all native letters have weight one or two. Every native preprocessing operation is nonincreasing for this weight: internal transitions preserve bases, cleanup deletes cells or replaces an anchor by an anchor, workspace is trimmed rather than inserted, and C P D ↦ Q ω α Q has weight four on both sides. Give c(h) weight 4+W_H(h), κ(k,p) weight 8+W_K(k)+|p|, and a group-code atom weight 8+|g|. Native H letters have weight one. Equality input weight is the sum of its two words.

Parsing r≥1 native code blocks into an atom costs at most 8+2r, versus Dr≥16r before parsing (the K and P projections together use r decoded letters, each of weight at most two). Combining atoms removes overhead. Replacing a run of t≥2 full raw sectors by c of their concatenated payload saves at least 3t−4≥2; an existing semantic sector has overhead four and only improves the saving. All other symbolic normalization steps are nonincreasing.

The recursive-call ledger is now explicit:

* K comparison of c(h),c(h') calls H equality on h,h', losing eight overhead units.
* K comparison of c(h) with native raw(w) calls H equality on h,w and literal irreducibility of w, losing at least seven units in the equality call.
* H zero/identity testing of κ(k,p) calls K comparison of k with Ω/empty, losing at least seven units.
* H final comparison of two κ atoms calls K equality of their k arguments, losing sixteen units (P equality is direct).
* H selector matching compares one κ(k,p) with a literal code C(v) in a tuple member of length <N_j. The K call adds at most 2|v|<2N_j/D to W_K(k), while the parent has the atom overhead and at least 2N_j+2 native marker units. No other opaque argument is duplicated into that call.
* Eligibility of selector j is assigned measure 2N_j+1. A parent containing its marker runs has measure at least 2N_j+2. Eligibility tests each tuple member separately with literal length <N_j.
* Literal irreducibility of a word of length L makes static-minimum K calls of weight at most 4L/D<L, or eligibility calls with 2N_j+2≤L. Group tests use the supplied polynomial-space algorithm directly.

Thus every recursive call has strictly smaller integer weight. A frame stores at most a polynomial in its input weight: two current decorated words, bounded enumeration counters, a single native machine configuration or candidate literal representative, and a single selector member. No accumulated table or full graph is stored. Since the stack depth is at most the initial weight, the total space is polynomial in that initial weight. This establishes the evaluator budget subject to the semantic normalization and tokenization claims above; those claims still need adversarial checking before a complete candidate is declared.

## Algebraic closure identity

For every K basis element b, including Ω interpreted as algebra zero, the source formula φ=iρ(−⊗(e0−e1)) gives

    φ(b) = c(κ(b,e0)) − c(κ(b,e1)).

The c(ζ) corrections cancel. If b=Ω both terms are c(ζ), so the formula still gives zero. Thus a chosen term in the expansion of a mixed-iterate algebra expression acquires one semantic wrapper at each application of φ; it does not acquire an expanded canonical code word. This is the proposed bridge to the affine mapping torus. It does not yet establish any space bound for arbitrary arithmetic circuits or arbitrary compressed group words.
