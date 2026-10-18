# From decorated equality to the frozen simple-envelope target

Author-side proof assembly. This document depends on the exact decorated evaluator, including its decreasing call measure; no generic compressed-word oracle is assumed.

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

This proves a polynomial-space word algorithm for S, assuming the decorated-equality lemma. It uses classical brick composition directly, and does not claim a new general twisted-group construction.

## 5. Full target assembly

The composition G→Γ→S is injective. S is nontrivial, finitely presented and simple by the cited source contracts; Section 4 proves the required polynomial-space word problem. A finite list of words for images of the input generators exists in the chosen finite alphabet of S; these can also be found by enumerating words and comparing their finite tables. No uniform polynomial in the descriptions of the input machines is asserted. No F∞ claim is appended. The remaining author-side task is to finish and audit the decorated-normalization lemma and compare the complete mechanism with the actual primary literature before offering a candidate to the independent gates.
