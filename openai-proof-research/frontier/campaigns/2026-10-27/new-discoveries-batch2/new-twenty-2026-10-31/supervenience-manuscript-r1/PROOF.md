# Ordinary proof (DRAFT; zero credit)


## 2. Exact expressivity question and the guard
Following [1, Definition 6], L_b is at least as expressive as L_a if for every F ∈ L_a there exists H ∈ L_b such that for every model M in the common class and every world w, M,w ⊨ F iff M,w ⊨ H. The equivalent H must be chosen independently of M and w. “More expressive” means at least as expressive, with failure of the converse.

Fan's Conjecture 15 [1, printed p. 17] asserts: for every n ∈ ℕ, Lₙ₊₁ is more expressive than Lₙ. More explicitly, the strict direction requires
@ ∀n ∈ ℕ, ∃F ∈ Lₙ₊₁, ∀H ∈ Lₙ, ∃(M,w),
@                  (M,w ⊨ F) ≠ (M,w ⊨ H).
The other direction is already available: add a tautological determining input and recursively translate the remaining arguments. We disprove the displayed condition at n = 1. A single failed adjacent step refutes the universal conjecture; it does not overturn the established strictness of L₁ over L₀.

### Lemma 1 (guard identity)
For arbitrary formulas A,B in L₁ define G(A,B) = D₁(A; A ∧ B). On every pointed ternary model,
@ M,w ⊨ G(A,B)  iff
@ ∀u,v, S(w,u,v) → (M,u ⊨ A) → (M,v ⊨ A)
@                         → (M,u ⊨ B ↔ M,v ⊨ B).

Proof. Suppose G holds. If S(w,u,v) and A is true at both endpoints, agreement on A holds automatically. The consequent of the D₁ clause is agreement on A ∧ B. Since A is true at both endpoints, that is exactly agreement on B.

Conversely, assume the right side. Consider an S-pair agreeing on A. If A is true at both endpoints, restricted B-agreement yields agreement on A ∧ B. If A is false at both endpoints, both conjunctions are false and agree. These exhaust the agreeing cases. If A differs between endpoints, the D₁ antecedent imposes no requirement. Thus G holds. QED.

The guard filters the actual relation pairs; it does not demand constant truth on an entire cell in W. Two disconnected pieces of a cell may assign different truth values to B. Nor does the guard require equal values of B on crossing pairs. This distinction is essential when S_w is not a complete product relation.

The identity remains valid for loops, repeated endpoints, asymmetric relation slices and empty slices. It applies to modal A and B as well as letters: its proof uses only their endpoint truth values, with no restrictions on how those values were obtained.


## 3. Four cells and recursive elimination
Put C₁ = A ∧ C, C₂ = A ∧ ¬C, C₃ = ¬A ∧ C, and C₄ = ¬A ∧ ¬C. These cells partition W according to the two truth values. Define
@ Split(A,C;B) =
@   (G(C₁,B) ∧ G(C₂,B)) ∧ (G(C₃,B) ∧ G(C₄,B)).

### Lemma 2 (four-cell decomposition)
On arbitrary ternary frames, D₂(A,C;B) and Split(A,C;B) have the same truth value at every world.

Proof. Suppose D₂ holds and an S(w,u,v) pair lies inside one cell Cⱼ. The endpoints agree on both A and C, so they agree on B. Lemma 1 gives G(Cⱼ,B), for each j. Conversely, suppose all four guards hold. For an S-pair agreeing on A and C, choose the unique cell determined by the two truth values at u. Agreement puts v in that same cell. Its guard yields B-agreement, which is precisely the D₂ requirement. QED.

The Boolean-cell method is not claimed as new. Fan [1, Section 6.1, Proposition 16] uses such cells to eliminate finite determinacy arity over ordinary Kripke frames by formulas involving noncontingency. Goranko and Kuusisto [2, Proposition 3.3 and proof] use Boolean types in a universal-frame determinacy setting. Those results provide the partition technique. They do not themselves give this arbitrary-ternary unary definition: the ordinary-frame formulas exploit product slices, and the universal-frame formulas use their own global setting. Lemma 1 supplies the missing expression of restricted agreement without imposing either frame condition. No claim of inventing cells or the restricted-agreement semantic notion is intended.

### Theorem 3 (uniform translation)
There is a map t : L₂ → L₁ such that for all F ∈ L₂, every M and every w, M,w ⊨ t(F) iff M,w ⊨ F. Define it by recursion:
@ t(p) = p;   t(¬F) = ¬t(F);   t(F ∧ H) = t(F) ∧ t(H);
@ t(D₂(A,C;B)) = Split(t(A),t(C);t(B)).

Proof. Use structural induction on F, with induction hypotheses quantified over every world. The atomic case is immediate; the negation and conjunction cases follow from the Boolean truth clauses. At a modal node, Lemma 2 reduces the translated formula to the D₂ truth condition for t(A), t(C), t(B). For every pair u,v, the induction hypotheses replace each translated argument at both endpoints by its original argument. The resulting condition is exactly that for D₂(A,C;B). This proves the modal case and the induction. QED.

Quantifying the induction hypotheses over all worlds matters: subformulas are evaluated at u and v, not just at the original w. Thus the proof includes nested dependence formulas in determining and dependent positions; it is not merely a one-step substitution on atomic inputs.


## 4. Consequences and the published obstruction
### Corollary 4
L₂ and L₁ are equally expressive on arbitrary ternary frames. Hence Conjecture 15 is false at n = 1.

Proof. Theorem 3 supplies the missing direction. For the converse translate D₁(A;B) to D₂(⊤,A;B), recursively translating A,B; the extra agreement condition is always true. Both maps are uniform in the pointed model. Therefore strictness at this adjacent step fails. QED.

### Corollary 5 (Section 7.3)
The relativized agreement language of [1, Section 7.3] is equally expressive as L₁. Its operator O(A,B) has exactly the right-hand semantics of Lemma 1, so O(A,B) is defined by D₁(A;A ∧ B). Recursively replacing O proves the language translation, including nesting. The reverse translation is the source's own identity D₁(A;B) ≡ O(A,B) ∧ O(¬A,B). Thus the Section 7.3 strict-expressivity conjecture, including the proposed undefinability of O(p,q), fails.

This consequence uses a known semantic operator and a new-to-this-dossier definition in the unary language; it is not a proposal to rename the guard as a new semantic notion. Section 7.4's existing decomposition of relativized supervenience into relativized agreement can also be combined with Lemma 1. That further observation is not a separate campaign nomination or a separate formal endpoint here.

### Humberstone (2019), pp. 16-17
Humberstone [3] explicitly adopts the same arbitrary ternary semantics on p. 15, distinguishing it from product-frame determinacy. On p. 16 he asserts that D₂ cannot be defined from the Boolean connectives and D₁, and argues that such a definition would require one formula χ whose agreement relation equals the intersection of those for the two determining formulas. The partition observation is sound: one bivalent formula supplies at most two equivalence classes, while two formulas can distinguish four nonempty Boolean cells.

What is insufficient is the claimed necessity of that compression. The partition argument rules out replacing two determining inputs by one formula χ having exactly their joint agreement relation. It does not rule out a Boolean compound of several D₁ formulas, and it does not restrict how their dependent arguments may use the determining formulas. Split uses four separate guards; each guard's dependent argument contains its own cell. No single χ encodes the four-cell partition. Therefore the proposed necessary condition is unnecessary for general definability, and Corollary 4 corrects the stated D₂-from-D₁ undefinability assertion.

This correction concerns that specific assertion and its supporting necessity argument. It does not dispute the partition calculation, the demonstrated L₀-to-L₁ strictness, or the paper's other results. The lawful Monash repository PDF and its retrieval receipt are retained. We rely on the actual pp. 15-17 text, not a bibliographic inference about its semantics. We do not infer a claim of priority from the continued appearance of the contrary assertion in specialist literature.
