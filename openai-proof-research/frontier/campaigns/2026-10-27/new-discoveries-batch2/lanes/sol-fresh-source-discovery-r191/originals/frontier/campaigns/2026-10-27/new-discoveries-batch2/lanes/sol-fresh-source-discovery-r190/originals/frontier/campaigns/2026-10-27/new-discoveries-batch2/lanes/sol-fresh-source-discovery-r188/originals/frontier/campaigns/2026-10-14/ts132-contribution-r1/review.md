# TS132 independent contribution and eligibility review

**Verdict: SUBSTANTIAL, for the exact frozen full target.** Historical eligibility is supported by the bounded, operation-level comparisons below. This is a contribution gate, not a full-proof verdict, acceptance, publication recommendation without the remaining gates, or worldwide priority certificate. Campaign count remains 8/10.

## Reviewed claim and identity

For every real C>0, the claim supplies a nonconstant total Boolean function f on finitely many coordinates, invariant under a group transitive on **all** coordinates, with f(0)=0 and bs(f,0)>C s(f)^2. Here s is maximum ordinary sensitivity over all inputs. The claim also supplies a fixed alpha>2 and such functions F_m with bs(F_m,0)>=s(F_m)^alpha for every m and bs(F_m,0) tending to infinity. No spectral replacement, promise domain, row-only transitivity, cyclic invariance, graph-property condition, minterm-transitivity, or sensitivity o(n^(1/3)) is reviewed as a substitute.

The reviewed author packet is `fresh-structural-discovery-r27`, copied unchanged into `inputs/author/`:

- Manifest: `2fabba39b9b907f675c01162eae65b970236923ed5b14b611017a515f7eef267`.
- Full scope: `4f4f5103561d77dd475a5b8f50bbcd0d8989e102c18392ace80cb0b52a735984`.
- Candidate: `e1e93a97ddae2d47d32feb0fa464da93c32d4de661c93b63ac0e7ff785de310a`.

The detached-anchor author verifier was inspected and replayed successfully on these copied bytes. Its success establishes identity only. The contribution assessment comes from reading the candidate, the actual source operations, and the primary comparisons. The separately assigned proof review was not used to obtain this verdict.

## What is already paid

Pinned OpenAI family132 supplies the nested predicates, the entire four-profile ordinary/joint sensitivity argument, zero-input disjoint sensitive blocks, OR balancing, and composition amplification. Its random labelling excludes a constant-sized head-constant configuration on a regular tournament; it does not provide an automorphism group transitive on every row-position pair for that realization. TS132's displayed recurrences and their all-input interpretation are adaptations of that source argument, not a new sensitivity theorem credited to this candidate. The general superquadratic separation was already obtained by the stipulated source. [Pinned source main file](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/paper.tex).

Meiburg's rigorous construction bounds **spectral** sensitivity through certificate-distance obstructions and a Gram-matrix estimate. His independent-label local lemma is already a structured obstruction method. Section 6.1 explicitly proposes cyclotomic labels on a Paley tournament, discusses transitive symmetry, and reports empirical spectral improvement. Thus Paley tournaments, algebraic labels, symmetry as a goal, and powering cannot receive new credit here. His stated spectral upper bound does not imply the required ordinary upper bound: lambda<=s has the wrong direction for that deduction. The main mathematical sections do not prove the fixed-depth first-difference head-constant exclusion used by TS132. [Meiburg v1, §§3–6](https://arxiv.org/pdf/2608.00851v1).

## The residual operation and why it clears this gate

The residual is a compatible labelled tournament, not the arithmetic replacement of 16 by 82. It must satisfy three requirements at once:

1. A head-constant subset has bounded size independent of the growing parameter.
2. The alphabet has size r=o(sqrt(k)), so it remains negligible in the source recurrence normalized at M approximately sqrt(k/2).
3. An actual group is transitive on the entire row-position set and transports the gate labels, so it preserves all nested predicates simultaneously.

The candidate achieves these requirements with k=p^4 rows, alphabet H of size r=(p-1)/2, and first differing coordinate labels. The quotient by the first coordinate is the operative obstruction: two distinct incoming quotient rows cannot have the same difference label at a fixed head. Every head-constant quotient therefore has indegree at most one and at most three vertices. The same statement holds recursively inside a fiber, giving at most 3^4=81 rows. The scalar-and-translation action transports these **same** labels and sends any pair (v,c) to any other pair. It does not merely move the rows while fixing inequivalent label positions.

There is a concrete tradeoff that this construction resolves. On a single Paley layer, retaining each nonzero square difference as its own label gives the same elementary incoming-label uniqueness, but r=(k-1)/2; then r/M is of order sqrt(k), outside the small-error regime. Compressing differences into a small cyclotomic alphabet restores a favorable alphabet size but loses the injective-difference reason that the quotient has indegree at most one. The fixed-depth lift retains the locally injective difference argument, increases the number of rows to p^4 without enlarging the alphabet, and makes the exclusion cost a constant rather than a growing function of p. Consequently r/M tends to zero and k/M^2 tends to two. This is the mechanism that allows the source proof to run inside the transitive class.

This is a short elementary construction using familiar operations. Neither lexicographic products nor affine actions are new, and their length or familiarity alone cannot decide the gate. My positive judgment rests on the new simultaneous compatibility argument: it replaces the source's symmetry-breaking existence interface by a deterministic exclusion construction that remains effective under the required group action. It is not a generic application of the old random-labelling conclusion, a parameter adjustment within it, a free symmetrization of a Boolean function, or another iteration of the already-paid ordinary recurrence. The downstream recurrence estimates, wreath invariance, OR construction, and fixed-power consequence are routine once this interface has been supplied; they are not additional contributions.

I considered a TECHNICAL disposition expressly, including the objection that the 3^h induction is a familiar product argument. The decisive distinction is that the product is being used to separate row growth from alphabet growth while retaining both the forbidden-pattern invariant and label covariance. Ordinary product closure of vertex transitivity alone gives neither the exclusion bound nor the required row/alphabet scaling. The candidate pays this compatibility in an explicit finite construction. That warrants SUBSTANTIAL in this campaign, with a narrow attribution of the new mechanism. This judgment does **not** require a reviewer considering TECHNICAL to find a literal duplicate theorem.

## Other primary operations checked

Chakraborty–Kayal–Paraashar construct total transitive pointer functions by coordinated raw-bit decoding, cell permutations, and pointer updates. Their §4 proof transfers specific query and degree bounds; §5 adds a desensitization/OR operation for sensitivity versus query complexity. These are genuine transitivity-preserving constructions, so an assertion that no such transfers exist would be false. The inspected transfers do not supply a low-sensitivity transitive version of an arbitrary source132 nested family, or a lower bound on zero-input block sensitivity strong enough for TS132. Table 1 still lists the quadratic Rubinstein separation for bs versus s. This comparison is about the actual interfaces, not an inference from that table alone. [Journal primary, §§3–5](https://dmtcs.episciences.org/15992/pdf).

Chakraborty's cyclic construction uses a partial assignment with a distinctive long zero pattern to control overlaps of almost-satisfied cyclic copies. Its sensitivity estimates are in terms of n and the pattern length; the minterm-transitive lower bound uses disjoint translates of one support. These do not give the compatible labels for the nested predicates. The distinction between arbitrary transitivity and one-orbit minterm representations is essential. TS132 does not claim the latter restriction or the sub-cubic-root sensitivity problem. [Chakraborty v1, Example 2.15 and §§3–4](https://arxiv.org/pdf/cs/0501026v1).

Kulkarni–Tal §4 averages translates of a minimal sensitive block to obtain a **fractional** block-sensitivity lower bound at zero. Their composition argument converts suitable fractional separations to block-sensitivity separations, and their OR/AND balancing already preserves transitivity. This does not make an arbitrary nontransitive input function transitive: their quantitative implication starts with an appropriately low-sensitivity transitive function. Therefore neither averaging nor powering can be credited to TS132, and neither removes the compatible-label construction it needs. [Kulkarni–Tal, §§2.2–4](https://eccc.weizmann.ac.il/report/2013/168/comment/1/download/).

Chaubal–Gál's inspected DNF argument controls sensitivity through a specified representation, certificate size, and number of terms. It is not a transitive superquadratic construction or an upper bound for every transitive function. The 2023 publication was located, but its full body was not read; this report does not assert equality of all its content with the retained 2020 version. [ECCC primary, Lemma 5 and Theorem 1](https://eccc.weizmann.ac.il/report/2020/134/download/).

## Historical eligibility and chronology

The actual family192 candidate in `fresh-structural-discovery-r25` was read in full. Its target is an unbounded linear-Fourier/degree ratio under cyclic invariance; its operation uses separated role intervals and disjoint cyclic event translates. It does not construct an equivariant gate labelling or bound head-constant subsets. Wreath-product symmetry is a shared standard tool, not a recycled contribution.

I147's **actual T2** was read, not dismissed from a search title. It seeks a total, uniformly evaluable bit-transitive near-quartic randomized-versus-quantum query separation. It records an unpaid transitive compiler for heterogeneous pointer roles and explicitly discusses the CKP decoder. TS132 does not solve that query target, use its missing compiler, or relabel its developed proof. Its label construction is a different operation on source132's homogeneous nested children.

Bounded searches covered proposals, canonical iterations, reviews, findings, and campaign reports. The retained results and the two substantive closest historical targets support eligibility. They are not an exhaustive semantic clearance of every old file. No source-family absence or missing accepted title is used as a sufficient eligibility criterion. The remaining inherited exclusions persist.

The author's chronology candidly states that the exclusion argument, affine action, and feasibility calculation were identified **before** scope freeze, with the full all-input proof and finite checks completed later. I accept that as pre-freeze feasibility work, not a previously sealed full proof. The frozen target is unchanged. This review does not independently certify a discovery timestamp or priority.

## Limits and required attribution

No unresolved comparator found in the inspected primary operations blocks this contribution verdict. Coverage remains bounded: the later Chaubal–Gál full body, CKP auxiliary balanced-pointer details outside the recorded ranges, every work cited by these papers, and all possible later papers were not exhaustively read. Current version checks and negative searches are navigation evidence only. The main relevant antecedents were read at their operative proof endings.

For a later manuscript, remove the author's suggestion that TECHNICAL requires an inspected general theorem reducing the construction. That is an inappropriate burden on the independent gate; a new assembly can still be routine. Also preserve the narrow attribution above: no claim to invent Paley symmetry, the ordinary/joint recurrence, OR balancing, or powering, and no claim to solve cyclic, minterm-transitive, graph-property, or n^(1/3) sensitivity questions. These are presentation requirements, not changes to the frozen mathematical target.

A separate full-proof gate and later manuscript/formal/release gates remain necessary. This review supplies no independent proof PASS and changes no count.

Original review prose: CC BY 4.0. Original verifier code: MIT. Myeongjin Kang, no affiliation, remains the candidate author. Third-party PDFs, extracted texts, and pinned source files retain their own rights and are private inputs. No public upload or shared-file edit was performed.
