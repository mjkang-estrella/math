# T247G independent contribution review, round 1

**Classification: TECHNICAL.** History eligibility: **ELIGIBLE** (bounded search). Not DUPLICATE, not INELIGIBLE, not BLOCKED.

This is the contribution gate only. Mathematical correctness of the full frozen claim is ASSUMED for this gate, as dispatched. No proof verdict, acceptance, priority, new-to-literature status or formal status is implied. Parent alone integrates.

## 1. Inputs and authentication

- Author packet `fresh-structural-discovery-r61/` (immutable, not modified). Before trusting its inventory, the author `verify.py` (SHA256 791fbd2c…, read first) was run read-only with the externally supplied anchor `38b748ab81407bdb6bbd6b8557fc9f4d27fc094884705e8fcd9963939c4907fd`: PASS, 62 payloads, 17 directories, 31 pinned blobs, 2 primary pairs. A zero anchor fails with rc=1. All nine named input hashes match the dispatch. Details: `input-authentication.json`.
- Anchor provenance is qualified exactly as the dispatch says: this anchor is the intake's fresh observation, not a recovered historical author seal. The scope timestamp 2026-10-18T11:33:15Z is after `tensor-mechanism.md` feasibility work. This review does not infer historical chronology from the current hash.
- Canonical source identities were rematched independently: `sources/preprints-tree.json` SHA256 eeecc1da… (13223 entries, `truncated=false`); all 31 retained blobs match tree Git SHA1s, including finite-rules.tex 7ba23dba… and cancellation.tex b52ff630….
- Copied author controls were rerun only in an authenticated disposable `/var/tmp` copy. Results: `author-controls-replay.json`.

## 2. Full frozen claim assessed

Exactly the dispatched FULL CLAIM, with no weakening: one infinite-dimensional, positively graded, nonunital associative F2-algebra A with finitely many degree-one generators, an ordinary finite homogeneous positive-degree presentation and finite-dimensional graded pieces, chosen BEFORE K, B, ell and T, such that for EVERY characteristic-two field K, EVERY associative K-algebra B (unital or not) all of whose finitely generated subalgebras have finite GK dimension, EVERY ell ≥ 1 and EVERY T in M_ell((K⊗A)⊗_K B), some T^N = 0. There is no common g or C, and N depends on the input. Excluded and not assessed as claims: A⊗A nil, finite GKdim(A), arbitrary-coefficient absorption, a uniform index, full formalization, literature priority.

Nothing in this review substitutes a weaker statement for that claim. The fixed-D and commutative observations in §4 are comparisons, not replacements.

## 3. Unpaid-operation comparison

"Paid" means the operation is already carried out, at operation level, in the pinned source (stipulated true) or in a primary body I read. The ranges are in `reading-limits.md`.

| # | Candidate step | Paid by | Unpaid residual | Weight |
|---|---|---|---|---|
| U1 | Lemma 1: squaring-height compiler, h_{j+1}=h_j² | Source `finite-rules.tex` states the compiler with the upper parameter as an explicit variable "Dh": data bits cDh (146–157), tape input enc(Dh) and lcDh data bits (655–670), Kleene fixed point with D chosen before it and a polynomial-time bound "at parameter Dh" (804–830). The source itself cites DRS §2.3 for the fixed point (800). DRS2012 §5 already pays variable zoom N_k under only the constraint that log N_k and the computation time are much smaller than N_{k−1}, with examples N_k ∝ 2^k and 2^(2^k). | Check that F(h)=h² keeps cF(h) ≤ q_h, the O(h²) input below T/4 and a predicate polynomial in h. These are the same inequality checks the source makes for Dh, with a polynomial instead of a linear upper parameter. log L ≈ h² is far inside the DRS allowance. | Routine parameter substitution (proof-gate item; correctness assumed here) |
| U2 | Alternation vanishes on a finite-dimensional subspace E without multiplicative closure | Source `ca:alternating` (field case); elementary multilinearity | Replacing M_d(K) by an arbitrary finite-dimensional E | Elementary (conceded by author and dispatch) |
| U3 | Lemma 2: direct packet cancellation with weights in M_d(V^s) | Source `ca:direct`: free packet-permutation orbit, eligible runs ≥ 2^h/100, distinct colors, exterior factors outside the alternator | Weights in a finite-dimensional subspace of M_d(B) instead of M_d(K); noncommuting coefficients stay in order | Routine extension |
| U4 | Lemma 3: cut reduction with coefficient-degree tracking s → kL_j s | Source `ca:cut-identity`, `ca:cut-reduction` (exact cut identity, unique literal cuts, bounded end pieces). Antecedent: Smoktunowicz 2008 §7 position-indexed matrices (Definition 7.1, Lemmas 7.1–7.2). | Record that a token weight is a product of at most kL_j lower weights, so its entries lie in V^{kL_j s} | Bookkeeping |
| U5 | Lemma 4: prefix automaton chunk→letter with entries kept in V^s | Source `ca:automaton` (prefix states, block extraction); Smoktunowicz 2008 §7; Schützenberger 1961 (source-cited only) | Identity transitions lie in V^s because 1 ∈ V | Bookkeeping |
| U6 | Coupled budget (2) and stopping level J | Source `ca:all-tests`, `ca:dimension-growth` (lines 381–414): log₂(d_j²) ≤ 2log₂d + O(j) + 2kcΣ_{i<j}h_i ≤ … + (2kc/(D−1))h_j, stop when 2^{h_J} > 400k d_J² | One extra additive term gΣ_{i<j}h_i + O(gj) of the identical form. Squaring makes Σ_{i<j}h_i ≤ 2√h_j = o(h_j). | Routine growth comparison |
| U7 | Central variable z, base change to K(z), coefficient extraction over B' | Source `thm:algebra`, `cor:nil-algebra` over every characteristic-two field, with the same z-extraction | Exactness of K' ⊗_K (−) preserves dim V^n; injectivity of M[z] → K(z)⊗M | Routine |
| U8 | Ordinary finite presentation, nonunital presentation, infinite dimension | Source `cor:nil-algebra`; `fr:faithful` nonzero encodings | None beyond Lemma 1 | Paid |
| U9 | Boundary remark: the growth hypothesis cannot be deleted (free coefficient algebra) | Standard free-algebra argument | None | Positioning only |

The only output of U1–U9 not literally present in a paid source is the **quantifier upgrade**: one presentation for all exponents g. It arises from U1 (a schedule change the source compiler and DRS §5 already allow) plus U6 (the fact that a superlinear schedule makes Σ_{i<j}h_i negligible against h_j). The dispatch states that a new quantified statement alone is insufficient. I find no further operation.

## 4. How much of the full claim the fixed-D source already covers

These are derivations in this review. They assume the candidate's Lemmas 2–4 (assumed correct at this gate) and the stipulated source. They are not source statements.

**(a) Bounded exponents.** Lemmas 2–4 use only the three conclusions of `prop:hierarchy`, not Lemma 1. Apply them to the unmodified source hierarchy h_j = h_0 D^j. Since Σ_{i=0}^{j−1}h_i = h_0(D^j−1)/(D−1) < h_j/(D−1), estimate (2) becomes

    log₂R_j ≤ O_input(1) + O_g(j) + ((2kc + g)/(D−1)) h_j.

Then h_j − log₂R_j → ∞ whenever g < D − 1 − 2kc. Source `ca:D` requires D > 10(c+1)(k+1) = 1,100,110 with c=10000 and k=10, so D − 1 − 2kc ≥ 900,110. Hence **every** fixed-D source algebra, by the candidate's own lemmas, already absorbs every coefficient algebra B whose finitely generated subalgebras have GK dimension below 900,110 (choose g strictly between that GK dimension and the bound).

**(b) Commutative coefficients of any finite GK dimension.** Let B be commutative and B₀ a finitely generated unital subalgebra containing the entries. B₀ is Noetherian, so its nilradical N satisfies N^r = 0, and B₀/N embeds into a finite product of fields L_i ⊇ K of characteristic two. Tensoring over K preserves this injection. The source's matrix nilness over every characteristic-two field makes the image of T nilpotent, so T^m ∈ M_ell(A_K ⊗ N) and (T^m)^r = 0. This uses no coefficient-degree budget and no Lemma 1.

**(c) Locally finite coefficients (g = 0).** A finite-dimensional unital B₀ embeds in M_n(K) by its regular representation, so M_ell(A_K⊗B₀) ↪ M_{ell·n}(A_K), which is source-paid.

Therefore the strict increment of the frozen claim over what the source plus routine extensions already give is absorption, by one presentation, of coefficient algebras that are neither commutative nor locally finite and have local GK dimension at least D − 1 − 2kc for the fixed source D. This does **not** show that a fixed-D source algebra fails absorption at large g. That question is not settled by the displayed estimate, by the candidate, or by this review. Changing D for each B would reverse the claimed quantifiers. As the dispatch notes, that observation alone does not establish substantiality.

## 5. Why TECHNICAL and not SUBSTANTIAL

1. Every mechanism the conclusion needs is paid: finite presentation, the local-rule compiler, self-reference, faithful simulation, rollback, cut grammar, free packet cancellation, the prefix automaton, central-variable extraction, all ell and all characteristic-two K.
2. The compiler change is a substitution of the upper parameter. The source writes it as a free symbol Dh, and DRS §5 already pays much faster variable zoom (2^(2^k)) than h → h².
3. The second resource (coefficient degree) costs log₂ dim V^{s_j} ≤ g·log₂ s_j + O(1) ≤ g·Σh_i + O(gj). This has the same shape as the paid state cost 2kcΣh_i, so the "coupling" is an additive term in one inequality.
4. Making Σ_{i<j}h_i = o(h_j) by choosing a superexponential schedule is a standard growth-compensation device. Any polynomial F with F(h)/h → ∞ works equally (for example h log h or h^{1+ε}), which confirms that the choice carries no structural content.
5. By §4, bounded-g absorption already follows from the fixed-D source with the same lemmas, and the commutative and locally finite cases follow from source matrix nilness. The remaining increment is the uniform-in-g quantifier.

For comparison, a SUBSTANTIAL contribution would need an operation not paid above. Examples: a cancellation mechanism for infinite-dimensional coefficient spaces, a separation theorem showing that fixed-D algebras fail absorption, or a route to A⊗A or arbitrary coefficients. None is claimed or present.

## 6. Why not DUPLICATE, INELIGIBLE or BLOCKED

- **Not DUPLICATE.** No source, companion, primary body I read, or project history item states this absorption or its fixed-D bounded-g analogue for noncommutative coefficient algebras.
  - Source/companion: the principal sections and ring-phases (`prop:ring-input`, `prop:hierarchy-input`, fixed geometric heights) contain no tensor/absorption corollary. A term grep over all family-247 TeX files found none. The pinned `lean/docs/247.md` covers only the periodic group.
  - Smoktunowicz arXiv 1403.2557v1 is a different operation: Golod–Shafarevich, Nullstellensatz over an algebraically closed field, D, I[D] and tensor-ideal descent give R⊗R and R⊗R^op nil. It has infinitely many relations and no universal coefficient class, and its tensor-square theorem is not implied here.
  - Smoktunowicz 2008 Theorem 1.2 is matrix-nil ⇒ Jacobson radical (with M_n(S)^j matrices nilpotent). It has no coefficient algebra class.
  - The 2026 Köthe papers go in the opposite direction: they construct nil algebras whose matrix rings or polynomial extensions are not nil or not Jacobson radical.
- **Not INELIGIBLE.** See §7.
- **Not BLOCKED.** The author's 2008 retrieval gap is closed: the Edinburgh Pure version of record was retrieved and §§1, 6–8 and the references were read. The remaining unread leads are recorded as bounded limits. They would affect literature priority, which is not claimed, rather than the operation-level classification. If any of them proves the all-g or bounded-g noncommutative absorption, the classification would move to DUPLICATE, not upward.

## 7. History eligibility: ELIGIBLE (bounded)

Family-247 history developments found:
- I07 `frontier/iterations/i07-structures.md` Candidate C (property (T)/nonamenability, residual finiteness; duplicate/routine).
- `proposals/algebra_geometry.md` line 129 (same theme).
- `fresh-structural-discovery-r15/screening.md` item 3 (finite-index inheritance and unbounded-order repackaging rejected).
- `frontier/scouts/discrete.md` §6 (group growth, screen only).
- r15 reading records, and the r32/r39 history indexes and r31/r64 catalogue title lists (titles and repeats only).
- `screen236.md` (prefreeze family-236 screen, no nomination); r60 prefreeze 076/179 provenance remains separate as dispatched.

None develops tensor absorption, coefficient algebras, Köthe/Krempa matrix conditions, or a variable-zoom compiler change. A focused search for `Köthe|Krempa|nil…tensor|tensor…nil|finitely presented nil` outside third-party/input copies and outside the author/T247G directories returned only catalogue title lines, a source-paper text copy (i79 `outside/`) and the NEW-TEN T247G entry (line 1452). Exact commands and exclusions are in `reading-limits.md`. This is not exhaustive clearance.

## 8. Required objections

Correctness is assumed, so these concern contribution positioning and credit. They do not change the TECHNICAL class, but any adoption text must satisfy them.

- **R1 (scope of the increment).** Candidate §7 says only that the fixed-D budget "does not establish this all-g statement". It must also state §4 of this review: by the same Lemmas 2–4, every fixed-D source algebra absorbs all coefficient algebras of local GK dimension below D − 1 − 2kc (≥ 900,110), and commutative or locally finite coefficients reduce to the source's matrix nilness over all characteristic-two fields. Otherwise the increment looks larger than it is.
- **R2 (Smoktunowicz 2008 and Krempa).** The author packet cites Smoktunowicz 2008 only from search snippets and does not cite Krempa at all. Credit Smoktunowicz 2008 (BLMS 40, 917–928) Theorem 1.2 and §7 (Definition 7.1, Lemmas 7.1–7.2) as the matrix-encoding antecedent of the prefix-automaton/cut bookkeeping. Credit Krempa 1972 (Fund. Math. 76, 121–130) for the matrix-nil/polynomial-ring/Köthe equivalences, as cited in Smoktunowicz 2008 §1 and both 2026 papers. Krempa's own body is unread here.
- **R3 (2026 Köthe refutations).** Positioning must cite arXiv 2609.07996v1 (Adamczewski–Böhmler–Marczinzik: for every countable field F, including F2, a nil F⟨b,c⟩₊ with a non-nilpotent 2×2 matrix) and arXiv 2609.15080v1 (Greenfeld–King–Vendramin: a finitely generated graded nil algebra with a point module, so A[t] is not Jacobson radical). They show that matrix and polynomial coefficient clauses are genuinely stronger than nilness. Those clauses are SOURCE-paid (the source proves matrix nilness over every characteristic-two field), so "every ell" and commutative coefficients must not be presented as candidate contributions.
- **R4 (finitely presented nil).** The source answers the finitely-presented-nil question (Ufnarovskij, Smoktunowicz 2008 Question 8.1). The adoption text must attribute the finite presentation and nilness to the source. The candidate already says this; keep it.
- **R5 (dependence on Lemma 1).** This classification is conditional on correctness, including the unreviewed Lemma 1 compiler substitution. It is not a proof verdict.
- **R6 (no priority).** No new-to-literature claim. The search was bounded and the leads in §10 are unread.

## 9. Optional objections

- **O1.** State that any polynomial upper parameter F with F(h)/h → ∞ works. Squaring is a convenience.
- **O2.** Whether a fixed-D source algebra already absorbs all finite-GK coefficient algebras is open here. A separation in either direction would change the interest of the statement, not this classification.
- **O3.** Label the free-algebra boundary remark in candidate §7 as standard.
- **O4.** A possible positioning remark is that A⊗_K N is nil for every nil N of locally finite GK dimension, for instance the finite-GK nil algebras of Lenagan–Smoktunowicz (unread lead). This relates to questions on tensor products of nil algebras (Puczyłowski 1993, cited in Smoktunowicz 2008 §8; unread). It needs literature checking before use.
- **O5.** The author's `integrity_controls.py` derives its anchor from the copy's own manifest, and its `changed_scope_status` case is rejected at the payload-hash step, so the scope pin line is never exercised. An extra control in this review exercises it (see `author-controls-replay.json`). This is an implementation note, not a contribution issue.
- **O6.** The masked "****" key observed in tool output for the author's `primary-receipts.json` is a display artifact. The actual bytes are `Smoktunowicz-1403.2557v1` (24 characters, no asterisks).

## 10. Mandatory credits and positioning

Mandatory credits:
- Pinned source family 247 (fd4aeeb2…): `prop:hierarchy`, the finite-rules compiler and fixed point, `fr:faithful`; cancellation `ca:alternating`, `ca:direct`, `ca:cut-identity`, `ca:cut-reduction`, `ca:automaton`, `ca:all-tests`, `thm:algebra`, `cor:nil-algebra`; companion `prop:ring-input` and `prop:hierarchy-input`.
- Durand–Romashchenko–Shen 2012, §2.3 (fixed point) and §5 (variable zoom).
- Smoktunowicz 2008 BLMS, Theorem 1.2 and §§6–7.
- Krempa 1972 (citation-level).
- Schützenberger 1961 (source-cited, unread).
- Smoktunowicz arXiv 1403.2557v1 as the distinct, closest tensor-nil construction (A⊗A and A⊗A^op), explicitly not implied.
- arXiv 2609.07996v1 and arXiv 2609.15080v1 as context.

Suggested positioning: "Assuming the pinned source, a squaring-height variant of its finitely presented nil algebra remains nil after tensoring with any coefficient algebra of locally finite GK dimension, uniformly in the growth exponent. The fixed-D source algebra already does so below an explicit GK threshold by the same estimates, and commutative or locally finite coefficients follow from the source's matrix nilness. The change is a schedule substitution permitted by variable-zoom self-simulation."

Unread literature leads (positioning only, no claims drawn): Bergman 1989 "Radicals, tensor products, and algebraicity"; Puczyłowski 1988 PAMS "Nil algebras with nonradical tensor square"; Puczyłowski 1993 "Some questions concerning radicals in associative rings"; Lawrence 1991 (Jacobson radical of tensor products; known only from Smoktunowicz 2008 §8 wording); Chebotar–Ke–Lee–Puczyłowski 2013; Ferrero–Puczyłowski; Krempa 1972/1979; Lenagan–Smoktunowicz(–Young); math/0505141.

## 11. Exact full-scope assessment

TECHNICAL applies to the full frozen claim with every quantifier as dispatched: a single A chosen first; an ordinary finite homogeneous presentation; all characteristic-two K, all ell, all T; B unital or nonunital with only local finite GK dimension and no common g or C; N depending on the input. No weaker fallback is used. History is ELIGIBLE under the recorded bounded search. The parent must still obtain an independent proof verdict, in particular for Lemma 1, before any acceptance.
