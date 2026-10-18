# T250P: polynomial-space simple envelopes

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Author-side complete proof claim, pending independent proof and contribution review. Source statements at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. Frozen scope is exactly scope250p.md; no F-infinity claim is added.

**Theorem.** Every finitely generated group G with deterministic polynomial-space word problem embeds in a nontrivial finitely presented simple group S with deterministic polynomial-space word problem. Finite and trivial G are included, and G need not be finitely presented. Polynomial degrees and constants may depend on the fixed input group and decider. Images of finitely many generators are finite words. There is no uniform polynomial over input machine descriptions and no claim about arbitrary compressed input words.

**Source contract and choices.** Use the pinned finite-envelope construction, its monoids K,H,T, compiler, contracted algebra B over F₂, nonunital injective map φ, and the affine-limit action. Its raw map is c([w])=raw(f(w)). Choose its allowed code length D at least 16 and large enough for the fixed alphabets. Enumerate tuples in length/lexicographic order of an explicit delimiter encoding and choose each spacing number N_j minimally subject to the printed inequalities. These are choices permitted by that construction; all proofs of confluence, embedding, finite presentation, kernel killing and the action are used at their stated scope. The higher-finiteness companions are not used to infer a complexity bound.

The proof's additional operation is a semantic evaluator for nested complete raw/code blocks. It avoids constructing the exponentially long canonical words hidden inside iterates of φ. Classical finite-component search, Britton reduction, coefficient parity counting and brick composition are separately credited in source-and-credit.md.

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

A potential selector contains 2N_j+2 native marker letters. Every tuple member at stage j has length <N_j. Eligibility requires each member to be irreducible under the static and earlier selected rules. Test one member at a time. For an arbitrary literal input w, first test absorption: the singleton ζ is irreducible, but every word of length greater than one containing ζ is reducible; the empty word is irreducible. This check is necessary for native raw payloads, although tuple members avoid ζ. For a remaining word, static code irreducibility is decided by searching all decoded words no greater than the current one in shortlex and comparing T/group values. Earlier selector tests recurse to words of length <N_i. Later selectors cannot fit in a member of the j-th tuple, since their marker lengths exceed its length. Literal irreducibility and selected-rule eligibility therefore admit the same bounded recursive evaluation.

## A strictly decreasing recursive-call measure

Use the following weight convention: give a native K letter its source grade, except that grade-zero workspace and Ω have weight one. Thus all native letters have weight one or two. Every native preprocessing operation is nonincreasing for this weight: internal transitions preserve bases, cleanup deletes cells or replaces an anchor by an anchor, workspace is trimmed rather than inserted, and C P D ↦ Q ω α Q has weight four on both sides. Give c(h) weight 4+W_H(h), κ(k,p) weight 8+W_K(k)+|p|, and a group-code atom weight 8+|g|. Native H letters have weight one. Equality input weight is the sum of its two words.

Parsing r≥1 native code blocks into an atom costs at most 8+2r, versus Dr≥16r before parsing (the K and P projections together use r decoded letters, each of weight at most two). Combining atoms removes overhead. Replacing a run of t≥2 full raw sectors by c of their concatenated payload saves at least 3t−4≥2; an existing semantic sector has overhead four and only improves the saving. All other symbolic normalization steps are nonincreasing.

The recursive-call ledger is now explicit:

* K comparison of c(h),c(h') calls H equality on h,h', losing eight overhead units.
* K comparison of c(h) with native raw(w) calls H equality on h,w and literal irreducibility of w, losing at least seven units in the equality call.
* H zero/identity testing of κ(k,p) calls K comparison of k with Ω/empty, losing at least seven units.
* H final comparison of two κ atoms calls K equality of their k arguments, losing sixteen units (P equality is direct).
* H selector matching compares one κ(k,p) with a literal code C(v) in a tuple member of length <N_j. The K call adds at most 2|v|<2N_j/D to W_K(k), while the parent has the atom overhead and at least 2N_j+2 native marker units. No other opaque argument is duplicated into that call.
* Eligibility of selector j is assigned measure 2N_j+1. A parent containing its marker runs has measure at least 2N_j+2. Eligibility tests each tuple member separately with literal length <N_j.
* Literal irreducibility of a word of length L makes static-minimum K calls of weight at most 4L/D<L, or eligibility calls with 2N_j+2≤L. Group tests use the supplied polynomial-space algorithm directly.

Thus every recursive call has strictly smaller integer weight. A frame stores at most a polynomial in its input weight: two current decorated words, bounded enumeration counters, a single native machine configuration or candidate literal representative, and a single selector member. No accumulated table or full graph is stored. Since the stack depth is at most the initial weight, the total space is polynomial in that initial weight. The semantic completeness verification below shows that these calls decide the stated equalities. Therefore equality of arbitrary finite decorated K/H words is decidable in polynomial space in their tree-encoding length. This is an ordinary deterministic algorithm, with no equality oracle remaining except the supplied polynomial-space G decider.

## Algebraic closure identity

For every K basis element b, including Ω interpreted as algebra zero, the source formula φ=iρ(−⊗(e0−e1)) gives

    φ(b) = c(κ(b,e0)) − c(κ(b,e1)).

The c(ζ) corrections cancel. If b=Ω both terms are c(ζ), so the formula still gives zero. Thus a chosen term in the expansion of a mixed-iterate algebra expression acquires one semantic wrapper at each application of φ; it does not acquire an expanded canonical code word. This is the bridge used below for the explicitly bounded affine expression family. No space bound for arbitrary arithmetic circuits or arbitrary compressed group words is inferred.

## Semantic completeness of the evaluator

The descriptions above specify a terminating equality algorithm, not merely a representation heuristic. Here are the points that connect its symbolic states to the source's literal normal forms.

First, a semantic c(h) expands to the *canonical* complete raw word raw(f(h)). Its α and ω are actual outer boundaries. In any compatible concatenation, the only incoming arrow to its initial vertex O is ω, and the only outgoing arrow from its final O is α. Thus it is a full sector separated from its neighbors by the source ωα cuts. A native machine component cannot contain any of its payload. Native preprocessing is therefore exactly the source preprocessing on the expanded input. Collapsing a maximal run of at least two raw sectors into one semantic c atom is exactly the source raw-run operation. Other native sectors are handled literally. Hence symbolic K outputs expand to the exact N outputs. Their comparisons are exact: canonical raw payloads compare by H equality; comparison to a literal raw payload additionally tests that the latter is H-irreducible.

Second, every nonempty canonical code is uniquely parsed into assigned length-D blocks starting with its own b symbol. No b occurs internally in a block, and the two code types have disjoint alphabets. A nonempty semantic code atom is therefore a complete valid run. A valid code cannot cross its boundary partially; the only crossing is concatenation of adjacent complete runs of the same type. Empty atoms are removed before reparsing, which explicitly handles newly adjacent native fragments. Canonicalizing a maximal run also canonicalizes all its subruns: replacing a nonleast subrepresentative would make the entire representative smaller in shortlex. Zero subruns force the entire T value to be zero. These are precisely the source static-rule operations.

Third, selectors have native d,l,r,h markers absent from both code alphabets. Every occurrence in the expanded state starts and ends among native markers and consumes each intervening code atom in its entirety. Enumerate all such native endpoint choices. For an eligible tuple word w_i, parse its native letters and maximal valid code runs. Its static irreducibility ensures every run is already a nonempty canonical representative. The candidate middle has exactly that literal string if and only if the native fragments match and the corresponding code values match. Thus recursive equality detects exactly the selector occurrences, even if a symbolic code atom denotes a very long word. There is no search over a guessed expanded length.

Finally, at termination the expanded symbolic H state has no absorption, static-code, or selector redex. Every symbolic modification is an equality in H, realized by source reductions of the expanded code runs and selectors. The source's confluence therefore identifies the result with f of the original expanded input. Unique tokenization makes final symbolic comparison equivalent to literal normal-form equality. Literal irreducibility first checks the absorption case just specified, then the exhaustive static-minimum and earlier-selector tests; finite tables are recomputed, not assumed available. In particular raw(aζ), for a native letter a, is not confused with c(ζ): its payload is reducible even though its H value is ζ. The strict call measure makes these mutually dependent procedures well-founded independently of expanded word length or stage depth.

A frame uses polynomial space in its weight: its finite trees have at most that many native/wrapper units; tuple encodings have O(j) symbols with j<N_j; native configurations and enumeration counters have polynomial size. Every child has smaller weight and each outer normalization is nonincreasing. Thus at most W frames of polynomial size in W are simultaneously retained. Direct HNN-group and partial-affine tests also use polynomial space in W. This proves the decorated-equality lemma with a polynomial depending only on the fixed source construction and supplied G machine.


# Affine and simple-group assembly

## 1. The input HNN group

For the source group Ĝ=⟨G×G,s | s(g,g)s⁻¹=(1,g)⟩, store each base block as a pair of literal G words (a,b). Charge it max(|a|,|b|). Multiplication of adjacent base blocks does not increase the sum of these charges. A forward pinch replaces a diagonal pair by (1,a); a reverse pinch replaces (1,b) by (b,b). Neither increases charge. The total starts at most the input length n. Tests use a b⁻¹ or a, hence G-query length at most 2n. There are at most n/2 pinches. This is a polynomial-space word algorithm for Ĝ, including finite/trivial G. It is the source Britton procedure with an explicit max-coordinate budget, not a new embedding construction.

## 2. Coefficient terms under the source self-embedding

Work over F₂. On a K basis element b, the source's φ=iρ(−⊗(e₀−e₁)) is exactly

    φ(b)=cκ(b,e₀)+cκ(b,e₁).

For b=Ω both terms agree and cancel; otherwise this follows because the two c(ζ) corrections in i cancel. For any literal K word b this formula applies to its basis class without first normalizing b. Consequently a chosen expansion term of φʳ(b) is a nested K decoration of size O(r+|b|), with r binary choices. No canonical code payload is expanded. A fixed polynomial expression in B has finitely many literal monomial terms, so the same applies to φʳ of any fixed coefficient.

For R=B⊗Bᵒᵖ, ψʳ(a⊗bᵒᵖ)=φʳ(a)⊗φʳ(b)ᵒᵖ. Tensor products multiply by (a,b)(c,d)=(ac,db); a basis pair vanishes exactly when one coordinate is Ω. The source transition on 6×6 matrices satisfies Fʳ(g)=I+ψʳ(g−I), by induction from its modified-identity formula. This identity must be retained: applying a nonunital map to I would be wrong.

Suppose an expression is obtained by multiplying at most n matrices of fixed dimension, each entry a sum of a fixed number of expressions φʳ(b) or tensor analogues, with r≤Cn and b from a fixed finite list of literal coefficient words. The corresponding affine-vector expressions have the same description with at most n insertion positions. Every distributed term has a decoration of size O(n²); the number of terms is at most 2^{O(n²)}. A term can be indexed and produced using O(n²) bits by choosing matrix indices, fixed coefficient summands and the binary branches of φ. This is a bound for this explicit family, not for arbitrary arithmetic circuits with shared multiplication gates.

To test such an F₂ sum for zero, enumerate a term i. Discard it if it is Ω (or has a zero tensor coordinate). Re-enumerate all terms j, toggling a bit whenever j has the same basis class as i, using decorated equality. If any nonzero term has odd multiplicity, the sum is nonzero; otherwise it is zero. Repeated tests of the same class are harmless. Two term counters, two polynomial-size terms and one equality call suffice. Thus coefficient equality is in polynomial space.

## 3. The affine group and its coordinate action

Use the source's exact isomorphism

    Γ ≅ (M∞⁶ ⋊ E∞) ⋊ Z,
    M∞=colim(B,φ),  E∞=colim(E₆(R),F).

Use base generators and t as the fixed alphabet of Γ, with fixed finite coefficient expressions. In a length-n word, a base factor at prefix t-exponent k contributes αᵏ of that factor. Put J=max(0, all these k), so J≤n. Its representative at stage J uses φ^{J−k} on its translation and F^{J−k} on its matrix, with 0≤J−k≤2n. For negative k this is the same formula obtained by first applying the inverse stage shift at stage zero. Thus this aligns representatives of the same element; it does not change that element by a stage shift. Collect the final stable exponent separately. Injectivity of φ and F makes equality at stage J exact. The word is trivial exactly when its stable exponent is zero, its translation vector vanishes and its matrix is I. Generate the affine products from these original base factors and matrix-index counters, not by repeatedly expanding a cumulative expression. Section 2 supplies the resulting tests in polynomial space.

More generally, fix a finite set P⊂X=M∞⁶ of coordinate labels, each with a finite stage/vector representative. Equality between g·x and h·y, where x,y∈P and g,h are words of length O(n), is decidable in polynomial space by aligning the resulting vector stages and using the same coefficient algorithm. This is the precise coordinate interface needed below. There is no assumption of a polynomial-size expanded coordinate vector.

The source supplies finite presentation of Γ, an embedding G→Γ, faithfulness and two-transitivity of Γ↷X, and finitely generated point stabilizers. We use all of these at their stated scope. The source's kernel-killing theorem is used through the displayed affine-limit isomorphism; no word algorithm for an uncontrolled Steinberg kernel is asserted.

## 4. Twisted Brin–Thompson word algorithm

Let S=XV_Γ for this action. The source and Zaremsky's type-(A) criterion give finite presentation; Belk–Zaremsky give the embedding Γ→S and simplicity. Choose a finite generating alphabet of S and fix a finite brick table for each generator and inverse. The union P of their finitely many coordinate labels is fixed. Every branch has the form h_b τ_g h_a⁻¹ on the brick B(a), with fixed finite prefix lists and fixed Γ words. All constants below depend on these tables.

Enumerate one table branch for each letter of an input word, discarding inconsistent itineraries. Maintain the composite branch as h_b τ_g h_a⁻¹. To compose on the left with h_d τ_h h_c⁻¹, compare the prefix constraints b,c. Their intersection is empty if any two constraints at the same coordinate are incomparable. Otherwise let e be their coordinatewise longer prefix, so B(e)=B(b)∩B(c). Put

    a'(s)=a(s) · ( e(gs) with prefix b(gs) deleted ),
    d'(t)=d(t) · ( e(h⁻¹t) with prefix c(h⁻¹t) deleted ).

The new branch is h_{d'} τ_{hg} h_{a'}⁻¹. This follows by pulling the common subbrick B(e) back through the first branch and forward through the second. Prefix deletion is valid precisely because e extends both b and c. Coordinate labels are stored as a Γ word applied to an element of P; they are compared by Section 3 rather than assumed distinct syntactically.

At each composition, the sum of lengths in a' increases by at most the fixed sum of lengths in c; the sum in d' is at most the old sum in b plus the fixed sum in d. New domain coordinates occur only where c extends b, so they are the current g⁻¹ applied to a fixed table coordinate. Old domain coordinates are unchanged. New range tails are old b coordinates transported by the fixed h; the prefixes d have fixed coordinates. This stores labels of length O(n), without repeatedly appending growing current twists to old labels. All prefix data consequently have total length O(n), with O(n) coordinates and twist word length O(n). An itinerary has O(n) choices from fixed finite sets, so exhaustive enumeration uses polynomial space.

On a nonempty brick, h_b τ_g h_a⁻¹ is the identity if and only if g=1 and a=b. Necessity of g=1 follows from faithfulness: if its coordinate permutation moves s, the independent infinite tails at s and g⁻¹s can be chosen differently, whatever finitely many prefixes have been prescribed. If g=1, different prefixes in a coordinate induce distinct prefix-replacement maps on its unrestricted tail. Sufficiency is immediate. Use the Γ word algorithm for g=1 and exact coordinate/prefix comparison for a=b. All consistent itineraries partition the domain, so the whole word is the identity exactly when every nonempty itinerary branch is the identity.

Together with the decorated-equality lemma proved above, this proves a polynomial-space word algorithm for S. It uses classical brick composition directly, and does not claim a new general twisted-group construction.

## 5. Full target assembly

The composition G→Γ→S is injective. S is nontrivial, finitely presented and simple by the cited source contracts; Section 4 proves the required polynomial-space word problem. A finite list of words for images of the input generators exists in the chosen finite alphabet of S; these can also be found by enumerating words and comparing their finite tables. No uniform polynomial in the descriptions of the input machines is asserted. No F∞ claim is appended. This proves the complete frozen target. The proof and contribution remain subject to independent gates; this author claim is not an acceptance verdict.
