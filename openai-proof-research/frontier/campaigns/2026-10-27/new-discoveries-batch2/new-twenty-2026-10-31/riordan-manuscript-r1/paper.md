# A 15-vertex counterexample to the odd-kernel conjecture for Riordan graphs

**DRAFT - MathDB 338258 - 3 November 2026**

Prepared with AI assistance by the manuscript agent in lane riordan-manuscript-r1. No human authorship or affiliation is asserted. This document is for root review; it is neither accepted nor published. Accepted credit: zero.

**Abstract.** Conjecture 7.7 of Cheon, Jung, Kitaev and Mojallal, *Riordan graphs II: Spectral properties*, asserts that every zero eigenvector of a singular io-decomposable Riordan graph of Bell type vanishes on odd vertices. We give an explicit graph on 15 vertices whose real adjacency kernel is one-dimensional and whose nonzero kernel vectors have nonzero odd part. Its generating polynomial is 1 + z + z^3 + z^6 + z^7 + z^8 + z^12 + z^13. The graph has the canonical odd copy required by a stronger form of the finite definition. It also arises from an infinite binary series satisfying h_(2j+1) = h_j at every index. Thus the counterexample survives both the finite-graph and infinite-family readings of io-decomposability. We explain the block cancellation that permits the example, describe two Lean endpoints in a frozen source packet, and delimit the computational and literature evidence.

## 1. Source, definitions and statement

Our primary text [1] is arXiv:1801.07021v1; the source access record lists no later arXiv version. The accepted manuscript in the Strathclyde repository [2] retains the conjecture. These bodies, their retrieval receipts, and the exact MathDB record are included in the dossier. The final publisher typeset body was not accessed. Throughout, vertices are numbered from 1, and kernels and ranks are over the real numbers unless explicitly stated otherwise.

For integer formal series g and f with f(0) = 0, the Riordan matrix (g,f) has entry [z^i]g f^j at zero-based position (i,j). The binary Riordan matrix B(g,f) reduces each coefficient modulo 2 to its representative in {0,1}. Definition 2.2 of [1] defines the simple Riordan graph by

```text
A(G_n(g,f)) = B(zg,f)_n + B(zg,f)_n^T.
```

Here the subscript denotes the leading principal matrix. B(zg,f) is strictly lower triangular, so the sum is an ordinary symmetric 0/1 matrix. A proper binary Riordan graph has odd g(0) and odd linear coefficient of f. In the Bell case f = zg these conditions both follow from odd g(0).

Write V_o = {1,3,5,...} and V_e = {2,4,6,...}, restricted to [n]. Definition 2.9 of [1] calls G_n(g,f) io-decomposable when the even induced graph is null and the odd induced graph is isomorphic to G_ceil(n/2)(g,f). We will verify the stronger canonical equality: vertex 2r-1 in the odd graph corresponds to vertex r in the smaller graph.

A graph is singular when its adjacency matrix has nonzero kernel; its nullity is the dimension of that kernel. For X = (x_1,...,x_n)^T, let X_o = (x_1,x_3,...,x_(2ceil(n/2)-1))^T and X_e = (x_2,x_4,...,x_(2floor(n/2)))^T. The source uses X for an arbitrary eigenvector with eigenvalue zero.

**Conjecture 7.7 [1].** If G_n(g,zg) is singular and io-decomposable, then X_o = 0 for every zero eigenvector X. Our refutation uses n = 15, away from any degenerate one-vertex endpoint.

<!-- PAGE -->
## 2. The spectral statements surrounding the conjecture

After ordering odd vertices before even vertices, an io-decomposable Bell graph with its canonical odd copy has adjacency

```text
             [ C    B ]
P^T A P  =   [        ],   C = A(G_ceil(n/2)(g,zg)).
             [ B^T  0 ]
```

B has ceil(n/2) rows and floor(n/2) columns. We reserve B in this block discussion for the odd-even block, distinguishing it from the full binary Riordan matrix B(g,f). In [1], Theorem 7.5 assumes odd constant coefficient and n ≥ 2 and asserts that D = [C; B^T], formed by stacking these matrices, has rank ceil(n/2). Lemma 7.6 asserts, for a zero eigenvector of a singular graph in this setting, that X_o = 0 if and only if B X_e = 0. Indeed, the two block equations are

```text
C X_o + B X_e = 0,            B^T X_o = 0.                 (1)
```

If B X_e = 0, these equations give D X_o = 0; full column rank then forces X_o = 0. They do not imply B X_e = 0 without that extra premise. The conjecture adds precisely a restriction that the rank theorem alone does not provide.

Theorem 7.8 of [1] states that the vanishing odd-part condition is equivalent to η(G_n) = η(B), where η denotes nullity. The eigenspace interpretation is necessary here: the condition means that every vector in ker A has zero odd part. Under that interpretation, ker A equals {0} × ker B exactly when the two dimensions agree, since {0} × ker B is always contained in ker A. We report the source statement in this natural universal sense; we do not infer a property of an arbitrary single selected vector from a dimension equality.

Lemma 2.11 of [1] states the Bell io characterization g^2 ≡ g′, equivalently g_(2j+1) ≡ g_j (mod 2). It cites *Riordan graphs I: Structural properties* [3]. The independently retrieved body of [3], Definition 4.1, Lemma 4.4 and Remark 4.5, supplies the finite definition and the coefficient characterization. Over characteristic 2, g^2 has only even powers and g′ extracts the odd coefficients, giving the displayed equivalence.

The finite and infinite formulations require a distinction. A fixed n-vertex graph only uses finitely many coefficients, and cannot constrain unused coefficients of an arbitrary chosen generating series. Thus the unqualified recurrence at every j is a family condition, or requires a truncation convention when used for a finite graph. We establish the finite definition directly and separately exhibit an infinite extension satisfying the full recurrence. No equivalence between arbitrary finite odd-copy isomorphisms and an identity on all coefficients is used.

**Proposition 1.** There exists a proper Bell Riordan graph on 15 vertices satisfying the canonical odd-copy identity and having an independent even set, together with a nonzero real kernel vector with nonzero odd part. The same graph is generated by a binary infinite series h with h(0) = 1 and h_(2j+1) = h_j for every j. Its adjacency nullity is 1.

Sections 3-5 prove this proposition by explicit coefficients and exact integer linear algebra. The nullity and the contextual block ranks are additional exact calculations; the Lean refutations need only the nonzero kernel certificate and its odd coordinate.

<!-- PAGE -->
## 3. The coefficient certificate and the matrix

Take

```text
g(z) = 1 + z + z^3 + z^6 + z^7 + z^8 + z^12 + z^13.       (2)
```

For zero-based i > j the lower adjacency coefficient is

```text
a_ij = ([z^i](zg)^(j+1)) mod 2
     = ([z^(i-j-1)]g^(j+1)) mod 2.                        (3)
```

The upper entries follow by symmetry and the diagonal is zero. Formula (3), with binary reduction before symmetrization, gives the following entire matrix in the original 1-based vertex order. Spaces separate columns; each line is one row.

```text
0 1 1 0 1 0 0 1 1 1 0 0 0 1 1
1 0 1 0 1 0 0 0 1 0 0 0 0 0 1
1 1 0 1 1 1 0 0 1 0 0 0 0 1 0
0 0 1 0 1 0 0 0 1 0 0 0 0 0 0
1 1 1 1 0 1 1 0 1 1 1 1 0 1 0
0 0 1 0 1 0 1 0 1 0 1 0 0 0 0
0 0 0 0 1 1 0 1 1 1 0 1 0 1 0
1 0 0 0 0 0 1 0 1 0 0 0 0 0 0
1 1 1 1 1 1 1 1 0 1 1 0 1 0 0
1 0 0 0 1 0 1 0 1 0 1 0 1 0 0
0 0 0 0 1 1 0 0 1 1 0 1 1 1 0
0 0 0 0 1 0 1 0 0 0 1 0 1 0 0
0 0 0 0 0 0 0 0 1 1 1 1 0 1 1
1 0 1 0 1 0 1 0 0 0 1 0 1 0 1
1 1 0 0 0 0 0 0 0 0 0 0 1 1 0
```

There is a simple finite recurrence for checking every displayed entry without manipulating infinite objects. Put p_(0,d) = 1 if d = 0 and 0 otherwise, and set

```text
p_(k+1,d) = sum_(t=0)^d g_t p_(k,d-t).
```

Then p_(k,d) = [z^d]g^k by induction on k. Substitute p_(j+1,i-j-1) into (3). Degrees at most 13 suffice. This recurrence also underlies the coefficient bridge in the formal packet. The manuscript's independent script scripts/check_math.py computes these integers directly and confirms the entire matrix, both io conditions, all entries of Ax, and the nonzero minor used below. It does not import discovery or review code.

Since g_0 = 1, all consecutive vertices are adjacent, so the graph is connected. Properness also follows immediately. Its matrix has no identical rows (checked in the retained independent-review certificate), so the exhibited kernel does not arise by subtracting a pair of twin vertices. The independent review further distinguishes its degree multiset from those of the 15-vertex Pascal and Catalan graphs; the mathematical refutation does not need this comparison.

<!-- PAGE -->
## 4. The io decomposition, kernel and nullity

Let C be the odd-odd 8 by 8 block and B the odd-even 8 by 7 block. Directly selecting entries from the matrix in Section 3 gives the following two blocks side by side. In each line the left eight entries belong to C and the right seven to B.

```text
0 1 1 0 1 0 0 1     |     1 0 0 1 1 0 1
1 0 1 0 1 0 0 0     |     1 1 1 0 0 0 1
1 1 0 1 1 1 0 0     |     1 1 1 0 1 1 1
0 0 1 0 1 0 0 0     |     0 0 1 1 1 1 1
1 1 1 1 0 1 1 0     |     1 1 1 1 1 0 0
0 0 1 0 1 0 1 0     |     0 0 1 0 1 1 1
0 0 0 0 1 1 0 1     |     0 0 0 0 1 1 1
1 0 0 0 0 0 1 0     |     1 0 0 0 0 0 1
```

The even-even block is the zero 7 by 7 matrix. Computing G_8(g,zg) by (3) gives precisely C: it is also the leading 8 by 8 principal matrix of Section 3. Thus both conditions of Definition 2.9 hold, with the canonical map r ↦ 2r-1. This verifies io-decomposability without appealing to an infinite characterization of the polynomial (2).

Define the integer vector

```text
x = (-1,1,0,0,-1,1,0,1,1,-2,0,1,1,-1,1)^T.
x_o = (-1,0,-1,0,1,0,1,1)^T,
x_e = ( 1,0, 1,1,-2,1,-1)^T.                             (4)
```

Multiplication of the displayed blocks gives

```text
C x_o = ( 1,-1,0,0,-1, 1, 2,0)^T,
B x_e = (-1, 1,0,0, 1,-1,-2,0)^T,
B^T x_o = (0,0,0,0,0,0,0)^T.                              (5)
```

Equations (1) and (5) prove Ax = 0 over the integers, hence over the reals. Since x_1 = -1, the vector is nonzero and has nonzero odd part. This already refutes Conjecture 7.7.

For completeness, let A_hat be the principal 14 by 14 matrix obtained by deleting vertex 1 from A. Exact elimination gives det(A_hat) = -1; the reproducible rational elimination is retained in scripts/check_math.py and qa/math-check.json. Thus rank A ≥ 14. The nonzero vector (4) gives rank A ≤ 14, so rank A = 14 and η(A) = 1. Every nonzero real kernel vector is therefore a nonzero scalar multiple of (4), and every such vector has nonzero odd part. The refutation also survives an existential reading requiring some nonzero zero eigenvector with zero odd part.

The independent review computes rank D = 8, rank B = 7 and η(B) = 0. Nothing contradicts Theorem 7.5: D has full column rank, but D x_o = (-B x_e,0)^T is not zero. Cancellation between C x_o and B x_e is the mechanism. Both sides of Lemma 7.6's equivalence are false, while the universal odd-vanishing assertion and η(A) = η(B) in Theorem 7.8 are both false. No proved source theorem is needed as a premise of the certificate.

<!-- PAGE -->
## 5. An infinite extension and the finite-definition caveat

For a positive integer u, write odd(u) for u with all factors of 2 removed. Define a binary coefficient sequence by

```text
h_m = 1 if odd(m+1) belongs to {1,7,9,13}; otherwise h_m = 0.
h(z) = sum_(e in {0,6,8,12}) sum_(k ≥ 0) z^((e+1)2^k-1).  (6)
```

The four supports in the sum are disjoint, by uniqueness of the odd part of a positive integer. Each coefficient is a finite, well-defined integer; no convergence is involved. Since odd(2(j+1)) = odd(j+1), equation (6) gives h_(2j+1) = h_j for every nonnegative j. Also h_0 = 1. Lemma 2.11's infinite recurrence is therefore satisfied literally, as well as modulo 2.

The coefficients of h through degree 13 are

```text
m:    0 1 2 3 4 5 6 7 8 9 10 11 12 13
h_m:  1 1 0 1 0 0 1 1 1 0  0  0  1  1.
```

They agree with (2). For any two coefficient sequences agreeing through degree d, the coefficients of every power agree through degree d: induction on the power uses only products a_t p_(k,d-t) with 0 ≤ t ≤ d. Formula (3) uses degree i-j-1 ≤ n-2 for every n-vertex entry. Consequently the graph of order n is local in the generating coefficients through degree n-2. In particular G_15(h,zh) = G_15(g,zg). This proves the infinite-family assertion of Proposition 1. The polynomial itself fails the infinite recurrence: g_15 = 0 while g_7 = 1. It must not be substituted for h in the infinite endpoint.

**Definitional remark (no separate result or credit claim).** If Definition 2.9 is read literally with arbitrary finite odd-copy isomorphism, the independent reviewer found an n = 7 example with g = 1+z+z^2+z^4+z^5. Vertices 1 and 5 have identical adjacency rows. Hence (-1,0,0,0,1,0,0)^T is a kernel vector with nonzero odd part. The even set is independent, and an odd-copy isomorphism is given in zero-based labels by (1,0,3,2): smaller vertex r maps to odd-subgraph position at that list entry. The odd copy is not canonically equal. This is retained to clarify the finite-definition issue, not offered as another discovery. The 15-vertex graph satisfies the stronger canonical and infinite conditions and avoids the twin mechanism.

**Computational extent.** The reviewer enumerated all binary prefixes with h_0 = 1 and h_(2j+1) = h_j that can affect G_n, for n = 2,...,15. The numbers of prefixes were 1,1,2,2,4,4,8,8,16,16,32,32,64,64 respectively. There were no counterexamples through n = 14 and exactly one at n = 15, mask 44, the present witness. This is computational evidence of minimality within that recurrence family, not a Lean minimality theorem or unconditional graph minimality assertion.

A separate review enumeration allowed all binary prefixes and arbitrary odd-copy isomorphism: 16,383 prefixes over n = 2,...,15. It found the finite-definition twin example first at n = 7. The isolated n = 1 endpoint, if admitted without the preceding n ≥ 2 context, is another degenerate obstruction; neither endpoint is the basis of our submitted 15-vertex certificate.

<!-- PAGE -->
## 6. Formal statement correspondence and proof architecture

The delivered proof packet is the byte-identical riordan-formal-r2 archive, SHA-256

```text
27175a85484d563031a12665736dbd4277de327cb726e1b6791d07a348c2c063
```

It contains 22 Lean modules: 20 proof modules and two audit-tooling modules. This manuscript lane safely extracts and hashes the archive but does not execute Lean, lake or leanchecker. The original finite endpoint and its proof sources are preserved. The additional infinite endpoint makes the extension argument a formal theorem as well.

| Mathematical object or statement | Lean definition or endpoint and scope |
| --- | --- |
| Polynomial and integer convolution, (2)-(3) | Core: gc, pc, polynomial coefficient lemmas, entry and sourceEntry; exact coefficient bridge |
| All 225 adjacency entries | Row0 through Row14 and Table: ordinary arithmetic proofs and assembled matrix identities |
| Canonical odd copy and independent even set | odd_copy and even_independent; zero-based even indices represent source odd vertices |
| Real nonzero kernel vector with nonzero odd part | Endpoint: xR, kernelR, odd coordinate at index 0; no mod-2 kernel substitution |
| Finite-definition refutation | Riordan.source_conjecture_false: negation of SourceConjecture, a sufficient polynomial/canonical specialization of the source universal assertion |
| Infinite binary series and every-index recurrence | InfiniteFamily: h, hZ, h_binary, h_io, h_zero, h_agrees; h uses ordCompl[2](m+1) |
| Locality and the literal Bell coefficient formula | seriesPow_local, seriesEntry_local, seriesBell_entry and h_bell_witness; truncation is proved harmless |
| Infinite-family refutation | Riordan.source_conjecture_false_infinite_family: negation of SourceConjectureInfiniteFamily, quantifying integer coefficient sequences |

The finite predicate specializes the source assertion to natural-coefficient polynomials and the stronger canonical odd-copy property. This strengthens its hypotheses, so a counterexample in this subclass refutes the broader finite claim. It does not purport to encode every possible finite isomorphism. The infinite predicate quantifies unrestricted integer coefficient functions a, assumes a_0 mod 2 = 1 and a_(2j+1) mod 2 = a_j mod 2 for every j, then quantifies n ≥ 2, singularity and every real kernel vector. Singularity is separately defined by the existence of a nonzero real kernel vector.

An integer formal series is represented by its unrestricted coefficient function; powers are finite convolution. EndpointStrong proves agreement with the literal polynomial Bell coefficient formula through seriesTrunc and seriesBell. It transports the frozen matrix certificate using h_witness, proves the two finite io conditions for h, and contradicts the universal conclusion with xR at index 0. No assumed equivalence between arbitrary finite isomorphisms and the infinite identity bridges the two endpoints.

The formal refutations certify the coefficient semantics, the relevant io properties and the kernel obstruction. Nullity 1, the contextual block ranks, the finite n = 7 remark, exhaustive search minimality and literature conclusions are ordinary mathematics or external audit evidence, not extra claimed Lean endpoints. This scope separation is essential to interpreting the packet.

<!-- PAGE -->
## 7. Audits, negative controls and trust limits

The independent review [4] built the earlier finite source packet from a safe extraction, with no supplied compiled artifacts. It reports 18 successful strict proof-module builds and 18 successful leanchecker checks. Its independent audit inventoried 398 local ordinary and generated declarations. The finite endpoint's reported axioms were exactly propext, Classical.choice and Quot.sound. That review concerned the earlier finite archive, SHA-256 beginning 628b850b, and must not be confused with an independent replay of the new infinite extension.

The formal-r2 report [5] records 22 strict builds and 22 separate leanchecker passes for the delivered extended packet. StrongAudit reports 450 local declarations from 20 proof modules and 10,694 declarations in their transitive type/body dependency closure. The tooling checks closure membership and audits the resulting dependencies, reporting zero unsafe or partial declarations, zero unsafe-recursion companions, no added axioms, and no local extern or implemented_by replacements. It inventories 57 upstream extern attributes and four upstream implemented_by attributes separately; the proof uses kernel bodies rather than those runtime replacements. This is a dependency-closure audit, not a rejection of all unrelated metaprogramming in imported mathlib.

Both endpoints are reported to use only propext, Classical.choice and Quot.sound. The forbidden mechanisms include sorry/admit, added axioms, unsafe proofs and native_decide. Audit metaprogramming is diagnostic tooling and is not a premise of the mathematical theorem. The reviewer and formal author report source scans and dependency checks in addition to the kernel checks. We preserve these reports as evidence with their exact original scope.

Three deliberately false formal-r2 controls are recorded as compilation failures: asserting the polynomial's infinite identity at j = 7; deleting odd part 7 from h's defining set while asserting the original h_6 value; and asserting a zero odd part for xR. These controls test sensitivity to the extension and kernel data. They are kept outside the successful source-only archive. Failure of a negative control is supporting audit evidence, not a substitute for checking the endpoints.

The toolchain is Lean 4.34.1 with mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. The pinned lake-manifest digest and Lean/leanchecker binary digests appear in evidence/formal-r2-results.json. Upstream mathlib and the installed binaries are trusted rather than independently rebuilt. Kernel soundness, the real-number formalization, and statement correspondence remain trust assumptions; a compiled theorem cannot itself establish bibliographic novelty or acceptance.

**Root replay evidence.** Root's replay-result.json, dated 3 November 2026 at 10:03:40 UTC, is now available and records PASS for a fresh extraction of the exact delivered archive: 22 builds, 22 leanchecker passes and three failed negative controls. It reports 450 local declarations and a 10,694-declaration dependency closure, with the allowed axiom union above. An initial setup failure occurred before any Lean call because the copied driver lacked a logs directory; the second clean extraction passed. This is root's recorded replay, not a prover execution by the manuscript lane. Acceptance and paper adjudication remain pending.

The manuscript lane independently recalculates the finite matrix with integer convolution and uses exact rational elimination. It checks Ax = 0, the two canonical io conditions, and det(A_hat) = -1. The source-only ZIP extraction rejects absolute paths, parent traversal, backslashes, symlinks, unexpected member types and compiled payloads. All frozen input hashes are compared before and after. Page images and a visual QA receipt accompany the manuscript. No formal prover is run in this lane.

Each authoring subprocess is capped at at most two CPUs, 120 CPU seconds, 140 wall seconds, MALLOC_ARENA_MAX=2, and a 6 GiB address-space bound with RSS sampling for the logged jobs. Only one heavy process runs at a time. The supplied reproduction scripts document how root can repeat the separate formal replay; this lane's checks do not replace that replay. Root alone decides source fidelity, significance, acceptance and any credit.

<!-- PAGE -->
## 8. Related work, access limits and bibliography

The literature screen is the independent reviewer's bounded investigation of 3 November 2026, retained in reviews/REVIEW.md with full retrieval receipts. Its live arXiv record check found only v1 of [1]. It read the institutional accepted manuscript [2], which retains Conjecture 7.7. The final publisher body was not accessed. OpenAlex returned nine citing records, including a duplicate preprint/journal pair; this is not a census of all later work.

The later actual bodies screened were Jung's *Diameter of io-decomposable Riordan graphs of the Bell type* [6], which refutes a different diameter conjecture; *Counting independent sets in Riordan graphs* [7], whose block decomposition and independence results did not yield the odd-kernel assertion; *Encoding labelled p-Riordan graphs* [8], on coefficient encodings; and *Oriented Riordan graphs and their fractal property* [9], in a different mod-3 skew-adjacency setting. *Families of Integral Cographs within a Triangular Array* [10] was screened at the level of its explicit graph families and spectra; the checked statements did not identify proper io-decomposable Bell examples giving this obstruction.

The source's own Section 5 distinguishes Catalan eigenvectors at eigenvalue -1 from Pascal zero eigenvectors. Theorem 5.6's specified nonzero Pascal coordinates are even vertices and do not already refute 7.7. The earlier *Spectral properties of Pascal graphs* [11] was located through an institutional record, but its full body was not independently obtained. This is an unresolved access limit. Search snippets, inaccessible publisher routes and missing bodies are not treated as clearance.

The review checked then-current public registry heads: OpenAI/math at 4eaee87548250b2682affda7d05d947c05554bae, and Omega at bbd7a670a08b1b14ca49992f2b3490462bed4f53. Its Omega comparison covered four commits and three unrelated paths since the candidate screen. Root's later registry-refresh.json records OpenAI/math unchanged and Omega at 6c90974127979efe1615cea5d287f97d438ea712; its complete D5 and Problems tree path screen and targeted read found only an unrelated Barry Riordan-Pascal determinant item. Neither registry screen is a full content audit. The reviewer comparison bounds changes since an earlier path screen; it is not a fresh reading of the complete registries. No matching public resolution was located within the recorded searches. We make no priority claim, worldwide novelty claim, or claim that the MathDB open label proves novelty.

**References.** ArXiv identifiers below specify retained preprint bodies. DOIs are omitted rather than inferred; journal-version access is separately documented by its original repository receipt.

[1] G.-S. Cheon, J.-H. Jung, S. Kitaev and S. A. Mojallal. *Riordan graphs II: Spectral properties*. arXiv:1801.07021v1 (2018). Definitions 2.2, 2.9; Lemma 2.11; Theorem 7.5; Lemma 7.6; Conjecture 7.7; Theorem 7.8.

[2] Same authors and title. Institutional accepted manuscript, Strathclyde repository. Dossier: sources/riordan-journal.pdf and its original HTTP/hash receipt. Conjecture 7.7 retained.

[3] G.-S. Cheon, J.-H. Jung, S. Kitaev and S. A. Mojallal. *Riordan graphs I: Structural properties*. arXiv:1710.04604. Definition 4.1; Lemma 4.4; Remark 4.5. Retrieved body in reviews/receipts/graphs-I.pdf.

[4] Independent review lane riordan-review-r1. *Independent adversarial review - MathDB 338258* (3 November 2026). Unpublished internal evidence, not a public mathematical reference.

[5] Formal lane riordan-formal-r2. Statement correspondence, results and reproduction reports (3 November 2026). Unpublished internal proof certificate with two endpoints.

[6] J.-H. Jung. *Diameter of io-decomposable Riordan graphs of the Bell type*. arXiv:1901.11156v1 (2019).

[7] G.-S. Cheon, J.-H. Jung, B. Kang, H. Kim, S.-R. Kim, S. Kitaev and S. A. Mojallal. *Counting independent sets in Riordan graphs*. arXiv:2006.16579v1 (2020).

[8] K. Iamthong, J.-H. Jung and S. Kitaev. *Encoding labelled p-Riordan graphs by words and pattern-avoiding permutations*. arXiv:2009.01410v1 (2020). Retained body: reviews/receipts/encoding.pdf.

[9] J.-H. Jung. *Oriented Riordan graphs and their fractal property*. arXiv:2009.01677v1 (2020). Retained body: reviews/receipts/oriented.pdf.

[10] H.-Y. Ching, R. Flórez and A. Mukherjee. *Families of Integral Cographs within a Triangular Array*. arXiv:2009.02770v1 (2020).

[11] G.-S. Cheon, J. S. Kim and S. A. Mojallal. *Spectral properties of Pascal graphs*. Institutional bibliographic record screened; full body not obtained. See review access limits.
