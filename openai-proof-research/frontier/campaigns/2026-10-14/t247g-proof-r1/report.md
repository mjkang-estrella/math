# T247G independent proof review, round 1

**Verdict: PASS_FULL_T247G.** No required repair, no gap and no counterexample was found against the full frozen claim. Seven optional editorial items are listed in Section 9. This is a proof verdict relative to the stipulated pinned source at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. It is not a contribution, novelty, formalization or acceptance verdict, and it does not assess contribution eligibility.

Reviewer: Claude Opus 5.5 (Factory Droid harness), assigned directory `frontier/campaigns/2026-10-14/t247g-proof-r1/` only. No nested agents. No parallel reviewer draft was read (none existed under `t247g-*` when listed). Nothing was staged, committed or uploaded.

## 0. Anchors and provenance

- All nine dispatch hashes match the present bytes of `fresh-structural-discovery-r61/` (MANIFEST.json `38b748ab…4907fd`, candidate.md `d15af71f…b36499`, original-scope.txt `19e05d71…b930c3`, verify.py `791fbd2c…cae0`, primary-comparison.md `9869d8ef…767b`, reading-limits.md `4a135447…7e915`, tensor-mechanism.md `2d608ca8…74e8`, checkpoint.md `40958cf8…dc9`, formal-scope.md `c6b09192…af7`). The author verifier, read before running, returned PASS (62 payloads, 17 directories, 31 pinned blobs, 2 primary pairs) with this anchor and rejected an all-zero anchor.
- The anchor is a **fresh parent-intake observation**, not an independently recovered historical author seal. It authenticates present bytes from that observation onward. It does not establish chronology. The recorded order is: feasibility exploration in `tensor-mechanism.md`, then a scope freeze stamped 2026-10-18T11:33:15.426854+00:00, then proof assembly. I do not treat the freeze as having preceded exploration. The asserted external scope message was not recovered by me either.
- Intake manifest `63f2d578…c6f897` verifies with `t247g-intake/verify-intake.py`, which I read first. It is used as implementation evidence only.
- `sources/preprints-tree.json` has SHA256 `eeecc1da…dc5e09b`, 13223 entries, `truncated=false`. I independently recomputed Git blob SHA-1 for all 31 retained bodies and matched each against that tree (`independent-checks.json`, part A). The operative files match the dispatch: finite-rules.tex blob `7ba23dba6390e947e121c2d86dffc3cbf6a636f0`, SHA256 `ab12219e94a9bf440c119f21768c6706b3d3be703bcfd6ade1244d5fb9ecdace`; cancellation.tex blob `b52ff630b3a50878ee59f3d7a0e3cf70d0d38bdb`, SHA256 `105759c220c6c048c888273302ffab5811a409b7d90a09bbfc8211c67638ef1c`; ring-phases.tex blob `3efd117f158209e3365fc4d953b6bb64aa53d9d7`.
- Author replay, in a disposable `/var/tmp` copy that was authenticated before and after use and then deleted (`author-replay.json`): all 13 author controls rejected or accepted with the expected reasons. `finite_diagnostics.py` output equals the saved JSON (4096 alternation tuples, 2032 automaton words, 6 samples). `seal.py` was read and never run.

## 1. Frozen claim checked

I checked the claim exactly as in `original-scope.txt` and the dispatch. There is one nonunital, positively graded, associative F₂-algebra A with these properties. It is finitely generated in degree one, has an ordinary finite homogeneous positive-degree presentation in the free nonunital algebra, is infinite-dimensional, and has finite-dimensional graded components. A is fixed first. Then, for every characteristic-two field K, every associative K-algebra B (unital or not) whose finitely generated subalgebras have finite GK dimension, every ℓ≥1 and every T∈M_ℓ((K⊗A)⊗_K B), some N≥1 has T^N=0. The growth hypothesis is local: each finite coefficient set lies in some V⊂B⁺ with 1∈V and dim V^n≤C(n+1)^g, with C and g depending on that set.

candidate.md states exactly this theorem (lines 7–15). It does not narrow K, B, ℓ or T, and it does not choose A or h₀ after g. It matches the intended scope in tensor-mechanism.md. No weaker fallback appears.

## 2. Candidate §2, Lemma 1: the squaring-height compiler delta

I read all 1047 lines of finite-rules.tex and reviewed Lemma 1 as a whole-compiler delta. The fixed-D proposition is **not** invoked as if it covered h↦h². The approach is to list every place where the upper parameter enters and check the replacement Dh→F(h)=h² there.

**Complete D-occurrence inventory** (`rg` over the file, then read in context). There are exactly these sites:

| Lines | Role | Replacement and status |
|---|---|---|
| 50–53, 103–105 | Statement; D fixed before the fixed point, h₀ after | F fixed before the fixed point; h₀ chosen after a. Valid for all h≥h₀. |
| 63–68, 83 | E_h:Σ_{Dh}→Σ_h^{L_h}; tokens' upper words over Σ_{Dh} | Σ_{h²}=all ch²-bit strings. L_h=2q_h+1 is unchanged. |
| 126 | Field ranges assigned "once D is fixed" | Assigned once F is fixed. The ranges are still integers ≤q_h. |
| 146–151, 211 | Data bit (idle) or two slots (locked) at core positions p≤cDh; need cDh≤q_h | p≤ch². This is a per-cell bit field, so the head and letter widths are unchanged. ch²≤2^h holds eventually. |
| 155–156, 1006 | Canonical block's core carries the upper letter's bits; normalized token gives one cDh-bit string per block | ch² bits per block, so the upper letter lies in Σ_{h²}, including its unused formats. |
| 344, 835, 843 | The certificate attests an entry of the parameter-Dh table | Entry of the parameter-h² table. |
| 659–663 | Initial tape: enc(\|a\|) a enc(Dh) enc(l) task data, with lcDh (or 2lcDh) data bits | enc(h²) and at most 2kch² data bits. This is O(h²) cells, below T/4=2^{⌊h/5⌋}/4 eventually. |
| 681 | β and the NAND circuit size are independent of a, D, h | Still independent: the universal machine is unchanged. |
| 753, 789 | Clause and address generation and the predicate run in poly(h) for fixed a, D | Fixed a, F. The new work is computing h² and an index into an O(h²) payload, which is polynomial. |
| 820–830 | Runtime at parameter Dh is polynomial, so it finishes before T for h≥h₀ | See "Runtime" below. |

No site uses linearity of Dh in h or a ratio between successive heights. The geometric relation h_j=h₀D^j enters only cancellation.tex (ca:D, ca:dimension-growth), which the candidate replaces by Section 5.

**Alphabet and arity.** Σ_h is still all ch-bit strings, with 32 integer slots of width 2h and 512 flags. The integers stored in letters are p, a, x≤q_h=2^h (h+1 bits), the clause index ≤m≤q_h, and l, b≤k. The new boundary ch² is never stored in a letter: the predicate computes it. Data are one bit per core cell (idle), or two slot bits plus one certificate bit (locked), so no upper payload enters the head. The head fields are unchanged: ε, phase, an O(h)-bit clause index and ρ∈{0,1}³. Relation lengths stay ≤2≤k. Tasks still have arity l≤k, and upper entries have length ≤2.

**Layout.** T=2^{⌊h/5⌋}, W=4T, o=2T. The certificate count βWT+g(W−2)(T−1) and the clause count (fr:clause-count) do not involve the upper parameter. Both are O(T²)=O(2^{2h/5})<q_h eventually, and the certificate fits in the first block's certificate field. Data addresses (slot, relative block ≤k, position ≤ch²) and certificate addresses are at most q_h.

**Predicate.** P_F(a,u;l,τ,data) uses the source predicate with these substitutions. It decodes at most k letters of cu bits. Syntax tests compare boundedly many O(u)-bit fields. A movement test generates the addresses of one clause. Initial-row lookup computes u² and indexes into enc(|a|) a enc(u²) enc(l) task data. The after-gate test evaluates a three-input function. Each step is polynomial in u for fixed a. The trivial-table fallback is decided by the same integer fit inequalities, which are also polynomial. P_F never runs a, never decides tableau existence, and never consults a table at another parameter. Each table is therefore an ordinary finite list, and no infinite presentation is assumed.

**Runtime.** With F fixed, t and a=s(t,t) are fixed. On level-h input x=(h²,l,τ,data), program a forms s(t,t) at constant cost and evaluates P_F(a,h²;…). That takes poly(h²)=poly(h) steps on an input of length O(h²). The source stipulates that universal simulation and return to the origin have polynomial overhead for each fixed program, so the total is poly(h). Choose h₀ after a such that, for every h≥h₀, all fit inequalities hold at h and the whole computation finishes before T. Then the inequalities also hold at h²≥h₀, so the level-h² table is the nontrivial one defined by the same predicate. This gives the exact tableau equivalence: a satisfying certificate at level h exists iff the input is an entry of the level-h² table. The single h₀ is valid for every later h, and it is fixed before any K, B or g appears.

**Arbitrary-word contracts.** Each of these lemmas reads the upper data only as "the slot and data bits at core positions ≤ the data bound". It is a statement about pair tests, interfaces, payload ownership or palette fields, and none uses the numerical value of the bound:

- **fr:context.** Structural tags never change. Interface checks per move, abutting regions, and ownership via creation only at an idle C(1) are unchanged.
- **fr:palette-soundness.** It involves colors, checker fields and swaps only.
- **fr:verification and fr:rollback.** They hold for any fixed payload and any finite addressed clause list with m≤q_h. Semantic zeros (A_j or Z_j with ρ≠0, false after-gate, zero-task success) remain zero declarations that never remove syntactic edges. Forged full-head states roll back by the same bijective tour argument.
- **fr:faithful.** The represented word is read from ch² bits per block via the unique owning head. Interleavings cannot alter a full region's payload, and success applies a genuine level-h² rule by the tableau equivalence.
- **fr:fragment-bound.** The bound is 16q_h+2, with B_h=(k+2)(17q_h+3).
- **fr:token-normalization.** Checker removal is supported in the palette and its preceding C(q_h). Rollback and release stay inside the acquired interval, giving an isolated normalization to E_h(u) with 1≤|u|≤k and |t|=L_h|u|.
- **Cuts and runs.** Cuts are recognized from single letters, so decompositions are literal and unique. The eligible run has length ≥(q_h−2)/16≥q_h/100.

A legal idle middle-core C(p) is nonzero at every h_j. The candidate's §2 summary (lines 29–41) states each of these points correctly. Lemma 1 holds.

## 3. Candidate §3, Lemma 2: alternation in a finite coefficient space

Alt_m is K-multilinear on any associative K-algebra, and it vanishes when X_i=X_j (i≠j) via the fixed-point-free involution σ↦(i j)∘σ in characteristic two. Expanding m>dim E arguments in a basis of E repeats a basis vector in every term. No closure, commutativity or PI hypothesis is used. For E=M_d(V^s)⊂M_d(B), dim E=d²·dim V^s.

The orbit partition is the source's ca:direct, which I read in full (cancellation.tex 123–204). Its selected run and packet depend only on the color-erased word, and whole-chunk permutations with unequal lengths fix that word, the run endpoints and the exterior chunks. Packet labels begin with distinct colors, so even duplicate identifiers yield m! distinct sequences. Zero sequences contain no member of a nonzero orbit. The coefficient enters only as U·Alt_m(X₁,…,X_m)·V⊗a. Here U and V are the ordered products of the exterior chunk weights, of any coefficient degree, and they stay outside the alternating factor. From r≥q_j/100, r≤mb+2b and (1), m≥r/b−2>d²dim V^s+1. Lemma 2 holds.

## 4. Candidate §4, Lemmas 3–4: cuts and automaton with two budgets

**Lemma 3** follows cancellation.tex 221–292, read in full. The sets are: 𝒫 = words of length ≤B_j with no cut letter, including the empty word; 𝒮 = words of length 1..B_j that begin with a cut letter and have no further cut; and the literal token list 𝒯_j indexes the upper chunk test with label u_t (labels may repeat). Concatenations p t₁⋯t_r s are literally unique. Zero concatenations and unrepresented zero words contribute 0⊗(anything)=0. For n≥N₀ every nonzero word is represented. Multiplication in M_d(B)⊗A_j is (X⊗a)(Y⊗b)=XY⊗ab, which preserves the coefficient order. Also id⊗E_j is an algebra map, and [t]_j=E_j[u_t]. M(t) is a product of |t|=L_j|u_t|≤kL_j letter matrices with entries in V^s, so its entries lie in V^{kL_j s}, using 1∈V. The bound for the specific upper test pulls back with threshold max(N₀, 2B_j+L_jN).

**Lemma 4** follows cancellation.tex 303–363. States are ε and the proper prefixes of labels. Identity transitions are I_d, closing transitions are W(v) (labels summed), parallel transitions are added, and the (ε,ε) block is the chunk sum. Entries are 0, 1 or sums of weights, so they lie in V^s with no degree increase (s≥1, 1∈V). The dimension is ≤b|Σ|^{b−1}d≤b|Σ|^b d. Zero padding is harmless for positive lengths. The empty-label case is handled by the source (all-zero letter matrices) and is trivial. The candidate omits it, which is optional item O3.

Cut and automaton costs are tracked separately and composed: cut sends (d,s)↦(d,kL_j s), and the automaton sends (d,s)↦(k|Σ_j|^k d,s). Neither cost is double counted or dropped.

## 5. Candidate §5: termination for one filtration

I recomputed both recurrences. The level-0 letter test has (d, V¹). Lemma 3 gives the level-1 chunk test with d₁=d and s₁=kL₀. At level j≥1, Lemma 4 then Lemma 3 give d_{j+1}=k|Σ_j|^k d_j and s_{j+1}=kL_j s_j. Hence d_j=d∏_{i=1}^{j−1}k|Σ_i|^k and s_j=∏_{i=0}^{j−1}kL_i. With |Σ_i|≤2^{ch_i} and kL_i≤3k·2^{h_i}:

- log₂d_j ≤ log₂d+(j−1)log₂k+kcΣ_{i=1}^{j−1}h_i
- log₂s_j ≤ j log₂(3k)+Σ_{i=0}^{j−1}h_i
- dim V^{s}≤C(s+1)^g≤C2^g s^g for s≥1

This gives exactly display (2), with the index ranges as printed.

For j≥1, h_{i+1}=h_i²≥2h_i, so Σ_{i=0}^{j−1}h_i≤2h_{j−1}=2√h_j. Also j≤log₂log₂h_j, so log₂R_j=O_input(1)+O_g(j)+(2kc+g)·2√h_j=o(h_j). There is therefore a J≥1 with log₂(400k)+log₂R_J<h_J, which gives 2^{h_J}>100k(R_J+3) (R_J≥1). Lemma 2 applies to the actual level-J chunk test, whose label bound is k, dimension ≤d_J and entries in V^{s_J}. Its eventual threshold pulls back through finitely many identities.

The quantifiers are: A, c, k, F, a and h₀ first; then K, B, ℓ, T; then V, C, g; then J and N. Nothing is uniform in g or C, and the presentation is not chosen after g. The vanishing is eventual in n, not at a single length. `independent-checks.json` parts C–D illustrate the arithmetic with exact integers, including g=10⁹. Their small h₀ values are arithmetic illustrations only, not valid compiler parameters.

**GK convention.** Suppose S is a finitely generated subalgebra of B with generating set X and finite GK dimension. Take V=K1+KX in B⁺. Then dim V^n=1+dim Σ_{i≤n}(KX)^i≤C(n+1)^g for any g above GKdim S, after enlarging C to cover finitely many small n. So the explicit local convention follows from the hypothesis. The scope states it explicitly in any case.

## 6. Candidate §6: presentation, infinite dimension, all K, B, ℓ, T

- **Presentation.** The finite relation set S consists of homogeneous binomials and zero words of positive length. Its ideal in the free nonunital algebra F₊ is span{usv}, with each context allowed to be empty, which equals the unital ideal (as in cor:nil-algebra). Hence A=F₊/(S)₊ and R=F₂⊕A, finitely generated in degree one with finite-dimensional graded pieces.
- **Infinite dimension.** The words E₀⋯E_{j−1}(a_j) are nonzero, with lengths L₀⋯L_{j−1} strictly increasing, so they are independent across degrees. Nothing here depends on K or B.
- **Nonunital B.** The injective algebra map B→B⁺ induces an injective ring map M_ℓ((K⊗A)⊗B)→M_ℓ((K⊗A)⊗B⁺), since tensoring over a field preserves injections. The hypothesis supplies V⊂B⁺ directly.
- **Expansion and scalar extension.** T=Σ_γW_γ⊗[v_γ]₀ with |v_γ|≥1 and |v_γ|≤b. Over K'=K(z) and B'=K'⊗B, the space (V')^n=K'⊗V^n by flatness, with the same dimensions, and zW_γ∈M_ℓ(V'). Section 5 is applied over K' using only V'. It does not use the theorem being proved, or any GK property of B', so there is no circularity.
- **Extraction.** M[z]→K(z)⊗_K M is injective for every K-vector space M, so P_n(z)=0 as a polynomial for n≥N. Since 1≤|v_γ|≤b, T^a=Σ_{n=a}^{ab}[z^a]P_n(z), which is 0 for a≥N. Noncommuting coefficient order is retained throughout. The template is the source's thm:algebra (cancellation.tex 448–536). The coefficient-growth input is new to that template.

## 7. Candidate §7 and exclusions

The free-algebra example is correct. For r=|Σ₀|≥2 generators, B=K⟨x₁,…,x_r⟩ has infinite GK dimension, and (Σa_i⊗x_i)^n has an independent free-word coefficient for each index sequence, at least one with a nonzero product in A, so it is not nilpotent. This is scoped only as a boundary, not as optimality. The remark about the fixed-D budget is correctly scoped as a limitation of that estimate, not a statement about any fixed-D algebra. The candidate does not claim A⊗A nil, finite GK(A), arbitrary-coefficient absorption, a uniform index, formalization or priority, and the proof does not need any of them.

## 8. Limits

- No formal (Lean) theorem exists for any part. formal-scope.md correctly says none was performed.
- The finite diagnostics (author and mine) do not establish the compiler, the orbit partition or universal termination.
- The verdict relies on the stipulated truth of the pinned source compiler, cancellation lemmas and universal-machine overhead statement, as the brief instructs.
- Primary papers (DRS2012, Smoktunowicz) were not read, because the proof does not use them.

## 9. Objections

**Required: none.**

**Optional (editorial; none affects validity):**

- **O1.** Lemma 1 would be easier to audit with the explicit D-occurrence table above, showing each site and its replacement.
- **O2.** State in Lemma 1 that the fit inequalities hold for every h≥h₀, and hence at h², so the level-h² table is nontrivial. The proof implies this but does not say it.
- **O3.** Lemma 4 should mention the empty-label case. It is trivial: the letter matrices are zero.
- **O4.** §6 says "first with B unital… V⊆B". The hypothesis supplies V⊂B⁺. Either work in B⁺ throughout, or note the unital projection B⁺→B for unital B.
- **O5.** Take N≥1 explicitly, for example max(N,1).
- **O6.** The final §5 inequality could cite the step log₂(100k(R+3))≤log₂(400k)+log₂R used to pass from o(h_j) to the strict inequality.
- **O7.** Candidate line 53 redefines the tests "as in S but with weights in M_d(B)". It would help to say explicitly that the source proofs of `ca:direct`, `ca:cut-reduction` and `ca:automaton` use the scalar coefficients only through ordered multiplication and linearity. The one exception is the count dim M_d(K)=d², which Lemma 2 replaces by dim E. With that change they rerun verbatim over M_d(B). I checked this in Sections 3–4 above.
