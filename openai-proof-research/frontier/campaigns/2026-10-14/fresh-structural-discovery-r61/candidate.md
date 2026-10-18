# T247G: a finitely presented nil algebra absorbing polynomial-growth coefficients

Author-side candidate; no independent proof/contribution verdict. Exact scope is `original-scope.txt` (SHA256 19e05d71ce3cf0478d81ddbf1cf3aacc2f089f07fc5ddbdb6ae8a9dbc1b930c3). It was frozen after feasibility derivation and before this proof assembly. The pinned source theorems are stipulated inputs, not audited here.

## Theorem and conventions

There is one infinite-dimensional positively graded nonunital associative F₂-algebra A, with finitely many degree-one generators and an ordinary finite homogeneous presentation, such that

    M_ell((K ⊗_{F₂} A) ⊗_K B)

is nil for every characteristic-two field K, every integer ell≥1, and every associative K-algebra B all of whose finitely generated subalgebras have finite Gelfand–Kirillov dimension. Nil means each element has some finite nilpotence index, not a uniform index. B may be nonunital.

We use the explicit equivalent growth convention: for every finite subset of B, its coefficients and 1 lie in a finite-dimensional subspace V of the unitization B⁺, with dim_K V^n ≤ C(n+1)^g for all n≥0, for some C≥1 and finite real g≥0. Here V^0=K1 and V^n is the span of products of n elements of V. The inclusion 1∈V makes the filtration increasing and V^a V^b⊆V^{a+b}. Finite GK dimension implies such a bound by choosing any exponent strictly above the limsup defining GK dimension, and increasing C to cover finitely many small n. Conversely the bound gives finite GK dimension. A finite set contained in a larger finitely generated algebra of finite GK dimension also satisfies this condition, by choosing a generating subspace of that larger algebra. Unitization changes the growth by at most one dimension. The zero coefficient algebra is trivial; henceforth a unital coefficient algebra may be taken nonzero, so dim V≥1. It suffices to prove the theorem for unital B: B embeds in B⁺, and tensoring over a field and taking finite matrices preserve this injection.

A is chosen before K, B and ell. No finite GK dimension of A, nilness of A⊗A, coefficient-algebra PI hypothesis, or uniform/effective nilpotence bound is asserted.

## 1. Source interface and inherited operations

Let S denote `An-infinite-finitely-presented-periodic-group-September-23-2026/build/` at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Exact canonical blob receipts are in `247-source-receipts.json`.

S `sections/finite-rules.tex`, Proposition `prop:hierarchy`, constructs, for fixed integer D≥2, alphabets Σ_h of size≤2^{ch}, c=10000 and k=10 permitted, at h=h₀D^j. Its homogeneous word replacements/zero declarations have length≤k. There are encodings from level Dh into level h of length L_h=2·2^h+1, preserving nonzero words and simulating each upper elementary relation. Long nonzero words have unique letter-recognized cuts into bounded end pieces and literal tokens. Each token equals an encoding of a nonempty upper word of length≤k and has the corresponding length multiple of L_h. Every sufficiently long nonzero word has a color-erased-recognizable eligible run of length≥2^h/100, whose letters can be permuted and whose colors are pairwise distinct.

S `sections/cancellation.tex` supplies the free packet-permutation orbit, the exact cut identity, prefix-state automaton, descending eventual-vanishing argument and central-variable extraction (`ca:direct`, `ca:cut-reduction`, `ca:automaton`, `ca:all-tests`, `thm:algebra`, `cor:nil-algebra`). We do not claim these as new. In particular the source already proves matrix nilness and works over every characteristic-two field. The changes proved below are the squaring-height compiler and the coefficient-filtration budget. The source statement with fixed D is not invoked as though it already states the modified hierarchy.

## 2. Squaring-height hierarchy

**Lemma 1.** The three conclusions of S Proposition `prop:hierarchy` hold with successive parameters h and h², along h_j=h₀^{2^j}, for one fixed sufficiently large integer h₀≥2, with the same absolute c,k and L_h=2·2^h+1.

**Proof.** We give the exact modification of the finite table construction, including its quantitative and logical dependencies. Fix the integer function F(h)=h² before constructing the program fixed point. In S `finite-rules.tex`, replace each upper-parameter occurrence Dh by F(h). No structural alphabet, head states, motion rule or palette rule is added. The alphabet at parameter h remains all ch-bit strings. Core positions 1,…,cF(h), in idle or locked tracks, store the data of one upper letter, in the same single-bit or two-slot format as the source. The data of that upper letter are distributed across core cells; they are NOT carried in an enlarged head. The canonical encoded block still has q_h=2^h core cells, q_h palette cells and one stop cell.

Use the source's universal deterministic tape machine and tableau layout unchanged, with T=2^{floor(h/5)}, W=4T, origin 2T. The initial tape now contains the fixed program a, enc(F(h)), enc(l), task type and at most 2lcF(h) data bits. For fixed a this is O(h²) bits. All input bits fit in fewer than T/4 positions for sufficiently large h. Tableau variables and clause counts remain exactly those in `fr:certificate-count` and `fr:clause-count`, hence O(T²)<q_h eventually. The head stores only the same constant number of metadata fields, three reading bits and an O(h)-bit clause index. Core/certificate/clause addresses are at most q_h; the source's 2h-bit integer slots remain sufficient. The new boundary cF(h) is below q_h eventually and is computable in polynomial time in h.

Define P_F(a,h;l,τ,data) by the source's membership predicate with these replacements. It examines a candidate rule of at most k letters of length ch each. A syntax test uses boundedly many O(h)-bit fields. A movement or gate test generates one addressed clause using the unchanged four-family formulas. Initial-row lookup now computes h² and selects its encoded bit or an addressed bit in the O(h²)-length payload. This takes polynomial time in h. It does not scan the entire tableau, run a, or decide the existence of a certificate. For small h whose explicit layout inequalities fail, use the same trivial table declaring every letter zero. Those inequalities also take polynomial time to test. Thus, for every fixed a, P_F(a,h;…) is a polynomial-time predicate in h.

Apply the source's explicit Kleene constructor: let t, on first input v, form s(v,v) and then evaluate P_F(s(v,v),x); set a=s(t,t). For this fixed a, evaluation of its own table predicate at parameter u has polynomial running time in u, including the fixed wrapper. Evaluating it at u=F(h)=h², and performing universal simulation and return to the origin, therefore takes polynomial time in h. Choose h₀ AFTER this fixed program so large that, for every h≥h₀, all layout inequalities hold and this entire computation finishes before T. A satisfying tableau at level h then exists exactly for an elementary entry of the level-h² table. This is an ordinary finite predicate for each table, not an infinite presentation or a call to a higher table while generating the lower table. The constants c,k do not grow with h or with the fixed program.

For clarity, the source's remaining invariants survive for concrete reasons. `fr:context` uses only the structural pairs, bounded number of blocks, and ownership of data/certificate slots; the number of data-bearing core positions is immaterial. `fr:palette-soundness` uses color counts, head flags and swaps, which are unchanged. `fr:verification` and `fr:rollback` use a fixed finite list of addressed clauses, frozen payload while a full head is present, and reversible traversal; the new list meets exactly the same address and truth-function contracts. In `fr:faithful`, the represented upstairs word is now read from ch² bits per block. Acquisitions and releases preserve that word; successful verification applies precisely an upper rule by the tableau equivalence just proved. Arbitrary interleavings cannot change another transaction's payload. Thus a clean encoding of a nonzero upper word cannot reach a zero declaration.

The arbitrary-word proof also does not use a linear relation between h and its successor. The unchanged structural and checker rules give the palette-fragment bound 16q_h+2 and cut-free interval bound B_h=(k+2)(17q_h+3). Between consecutive cuts there are at most k complete blocks and at most one transaction. Palette-head removal and rollback release the transaction, or produce zero; the latter is impossible inside a nonzero word. These replacements stay inside the token. Its remaining ch² data bits per block give an upper word of length between one and k. Normalization therefore has length L_h times that upper length. The finite token list and unique decomposition follow exactly from the cut criterion. The two head positions and at most sixteen homogeneous non-head intervals in a complete palette give an eligible run of length at least (q_h−2)/16≥q_h/100. Every argument uses the same relation lengths≤2≤k.

Finally a legal idle middle-core letter C(p), 1<p<q_h, is nonzero: no unary zero or cursor creation applies and a one-letter word admits no two-letter move. This proves all three hierarchy conclusions at every h_j. ∎

This lemma is a delta proof relative to S's complete local-rule implementation, not a claim to have reproduced all its tables independently. DRS2012 §§2.3 and5 already supply fixed-point and variable-zoom self-simulation as general operations; the specific polynomial h² overhead check above is required to apply them to S's word-rule/rollback compiler.

## 3. Alternation in a finite coefficient space

Let C be any associative unital K-algebra, K of characteristic two, and let E⊆C be a finite-dimensional K-linear subspace. For m>dim E,

    Alt_m(X₁,…,X_m)=Σ_{σ∈S_m} X_{σ(1)}⋯X_{σ(m)}=0       (X_i∈E).

Indeed the expression is multilinear and vanishes when two arguments agree: swapping their labels pairs equal products without fixed permutations, so characteristic two cancels each pair. Expand all arguments in a basis of E; every basis tuple has a repeated entry. E need not be closed under multiplication. With E=M_d(V^s), its dimension is d² dim V^s.

Define letter/chunk tests as in S but with weights in M_d(B). Algebra word images lie in the other tensor factor and hence commute with the coefficient factor; the coefficients themselves need not commute. A chunk test has finitely many identifiers, each a nonempty word of length≤b and a weight in M_d(V^s). Its length-n sum includes all sequences of chunks of total word length n, separately even when labels or segmentations coincide.

**Lemma 2 (direct filtered cancellation).** At level j, if

    q_j/100 > b(d² dim V^s + 3),                         (1)

then every such fixed chunk test eventually vanishes.

**Proof.** Use the source's first eligible run selected from the color-erased nonzero concatenation. Mark chunk boundaries, keep exterior and at most two crossing chunks fixed, and permute all m complete chunks inside the run. Since r≥q_j/100 and r≤mb+2b, (1) gives m>d²dim V^s. Whole-chunk permutations preserve the color-erased word, the chosen run, its endpoints and its algebra image. Its colors are distinct, so packet labels and hence identifiers are distinct: all m! permutations are separate sequences. Zero sequences cannot remove a member of a nonzero orbit because all members have the same algebra image. The packet procedure therefore partitions nonzero summands into free permutation orbits, even with unequal chunk lengths and multiple segmentations. An orbit contributes U Alt_m(X₁,…,X_m) V⊗a, which is zero by the preceding finite-space identity. Exterior products U,V may have arbitrarily high coefficient degree; they stay outside the alternating factor and impose no extra dimension requirement. ∎

## 4. The two budgets under reduction

**Lemma 3.** A level-j letter test of matrix dimension d and entry space V^s reduces by S's cuts to one level-(j+1) chunk test of dimension d, label bound k, and entry space V^{kL_js}. If that upper test eventually vanishes, so does the lower letter test.

**Proof.** For each literal token t choose the source's fixed upper label u_t, 1≤|u_t|≤k and |t|=L_j|u_t|. Give it weight M(t), a product of at most kL_j lower letter matrices, hence with entries in V^{kL_js}. The exact cut identity is

 S_{j,n}=Σ_{p,suffix} (M(p)⊗[p]) (id⊗E_j)(C_{(n−|p|−|suffix|)/L_j}) (M(suffix)⊗[suffix]),

summed only over nonnegative integral displayed lengths, for all sufficiently large n. Prefixes/suffixes range over finite sets of bounded length determined by the hierarchy. Unique literal cuts prevent multiplicity errors; zero words contribute zero. Every coefficient factor retains its order, so this identity is valid in M_d(B)⊗A_j. If C_m=0 for m≥N, every term vanishes when n≥2B_j+L_jN, also taking n above the cut threshold. ∎

**Lemma 4.** A level-j chunk test of dimension d, label bound b and entry space V^s is one fixed block of a letter test of dimension≤b|Σ_j|^b d, still with entry space V^s.

**Proof.** Combine weights having the same label by addition. Use the empty prefix and all proper prefixes as states. Continuing a prefix has weight I_d; completing a label v and returning to the empty prefix has weight W(v). Both transitions are allowed if v is simultaneously a label and proper prefix. Matrix blocks sum parallel transitions. Paths from empty prefix to empty prefix are exactly chunk segmentations, with the ordered weight product. There are at most Σ_{r=0}^{b−1}|Σ_j|^r≤b|Σ_j|^b states. Since s≥1 and 1∈V, identity entries lie in V^s; adding transitions does not increase degree. Matrix block extraction gives the identity, over any coefficient algebra. ∎

The two lemmas must be used together. Counting only matrix states loses the cost of the growing coefficient words. Counting only coefficients loses the repeated prefix-state expansion.

## 5. Termination for one fixed coefficient filtration

Fix K,B,V,C,g and a level-zero letter test of dimension d and entry space V (enlarge V to contain its finitely many entries). Set d₁=d and s₁=kL₀. For j≥1 set

    d_{j+1}=k|Σ_j|^k d_j,       s_{j+1}=kL_j s_j.

The first cut gives a level-one chunk test within these bounds. At each next step, Lemma4 changes chunk to letter without changing s_j, and Lemma3 changes level and multiplies degree by kL_j. Padding matrix dimensions with zero blocks is harmless. Every actual transformed test obeys these bounds, even if some labels/weights vanish.

Because L_i=2·2^{h_i}+1≤3·2^{h_i},

    log₂ d_j ≤ log₂d +(j−1)log₂k + kc Σ_{i=1}^{j−1}h_i,
    log₂ s_j ≤ j log₂(3k) + Σ_{i=0}^{j−1}h_i.

For s_j≥1, dim V^{s_j}≤C(s_j+1)^g≤C·2^g s_j^g. Therefore, writing R_j=d_j² dim V^{s_j}≥1,

    log₂ R_j ≤ 2log₂d + log₂C + g
       + 2(j−1)log₂k + gj log₂(3k)
       + 2kc Σ_{i=1}^{j−1}h_i + g Σ_{i=0}^{j−1}h_i.       (2)

Here all input-dependent constants are finite, but no upper bound on g was fixed when constructing A.

For h₀≥2 and h_{i+1}=h_i² we have h_{i+1}≥2h_i and hence Σ_{i=0}^{j−1}h_i≤2h_{j−1}=2√h_j. Also j/h_j→0. Dividing (2) by h_j shows log₂R_j/h_j→0. Consequently there is a finite J with

    2^{h_J}>100k(R_J+3).

Lemma2 kills the actual incoming level-J chunk test. Pull its eventual-vanishing threshold down through the finitely many Lemma3/4 identities. This proves eventual vanishing of the initial letter test. The threshold is allowed to depend on that test and its coefficient filtration; neither the cut thresholds nor the end-piece weights need be uniform over all inputs.

A level-zero chunk test with arbitrary finite label bound is converted first by Lemma4 to a finite-dimensional letter test. Choose V to contain all its entries and 1, as above. Thus EVERY fixed finite chunk test over B eventually vanishes. This is not an assertion that B itself satisfies a polynomial identity, nor a finite-dimensional representation of B.

## 6. One finite algebra and nilness of every tensor matrix

Let R be the unital level-zero algebra over F₂ in Lemma1 and A its positive-degree ideal. The alphabet Σ₀ is finite, and the table consists of finitely many homogeneous replacements and zero words of length≤k. Thus R is ordinarily finitely presented; no higher-level relations are appended. The same finite list presents A in the free nonunital algebra: the ideal generated by the list is spanned by products u r v with either context allowed empty, and all such products have positive degree. This ideal is identical in the unital and nonunital presentations. Therefore R=F₂⊕A and A has the asserted finite homogeneous presentation and finite-dimensional graded pieces.

For each j choose a nonzero middle-core letter a_j at level j. Iterated faithful encoding gives a nonzero level-zero word of length L₀⋯L_{j−1}. These lengths strictly increase, and the grading separates their nonzero images. Hence A is infinite-dimensional. This construction and its fixed h₀ do not depend on any coefficient field or algebra.

Fix K,B,ell as in the theorem, first with B unital. Any matrix T in M_ell(A_K⊗B) has a finite expansion

    T=Σ_γ W_γ ⊗ [v_γ]₀,

after swapping the two tensor factors, where W_γ∈M_ell(B), the v_γ are nonempty words and their lengths have some finite bound b. For an empty sum T=0. Choose a finite generating subspace V⊆B with 1 and every matrix entry, with dim V^n≤C(n+1)^g.

Adjoin one central indeterminate z and let K'=K(z), B'=K'⊗_K B. Put V'=K'⊗V inside B'. Exactness over a field gives (V')^n=K'⊗V^n and equality of the finite dimensions, so the same growth constants hold. The weights zW_γ belong to M_ell(V'). Section5 therefore supplies N with the length-n chunk sum zero over B' for all n≥N. Before localization that sum is the finite polynomial

    P_n(z)=Σ_{r, γ₁,…,γ_r: Σ|v_{γ_i}|=n}
       z^r W_{γ₁}⋯W_{γ_r} ⊗ [v_{γ₁}⋯v_{γ_r}]₀.

The canonical map M_ell(B⊗A_K)[z]→K(z)⊗_K M_ell(B⊗A_K) is injective: express its finitely many coefficients in a K-basis and use injectivity K[z]→K(z). Thus P_n=0 as an actual polynomial whenever n≥N, not merely after evaluation at a scalar. For a≥N,

    T^a = Σ_{n=a}^{ab} [z^a]P_n(z) = 0.

This respects all noncommutative coefficient products and different word lengths. The argument works for every characteristic-two K and every ell. Passing from B to B⁺ proves the nonunital case. This completes the full theorem. ∎

## 7. Exact boundary and contribution limits

The coefficient growth hypothesis cannot simply be deleted. If an algebra A is generated by a₁,…,a_r and is not nilpotent, then Σ_i a_i⊗x_i is not nilpotent in A⊗K K⟨x₁,…,x_r⟩. Its nth power has a distinct free-word basis vector for every length-n index sequence; at least one corresponding A-product is nonzero, since otherwise all longer words would vanish and A^n=0. This does not assert optimality of the finite-GK class.

The residual operation is a finite presentation chosen to absorb coefficient filtrations of arbitrarily large FIXED polynomial exponent, with the state and degree costs coupled in (2). For fixed D the analogous displayed budget has gΣh_i comparable to g h_j/(D−1), and does not establish this all-g statement for one fixed source presentation. This is a limitation of that budget, not a counterexample to any original fixed-D algebra. Changing D separately for each coefficient algebra would reverse the theorem's quantifiers.

The proof is relative to S's stipulated word compiler, and DRS already pays variable-zoom self-simulation. Packet alternation, cut reduction, automata and central-variable extraction are inherited. The coefficient-space extension of alternation itself is elementary. Whether their coupled use is substantial enough for the campaign is an independent contribution question; a new statement or a strong-looking universal quantifier is not alone evidence. No new-to-literature claim is made. All finite diagnostics and any scoped formal support are supplementary, not substitutes for Lemma1 or the full algebraic proof.
