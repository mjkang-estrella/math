# An explicit integral regular summand in every staircase tensor cube

**Myeongjin Kang**  
2026-10-14. No affiliation.

**Frozen submission candidate. Independent full-proof, contribution, and manuscript gates remain pending. No acceptance or campaign-count claim.** Original prose © 2026 Myeongjin Kang, [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); original code is MIT-licensed. Third-party source snapshots retain their own rights and notices; see [RIGHTS.md](RIGHTS.md).

We give a complete proposed construction of a split integral regular summand in the tensor cube of every staircase Specht lattice. The section-by-section proof defines a positionwise three-letter map, projects onto words with distinct triangular letters, and obtains coefficient exactly one on a single word. This proves a split identity before base change and therefore preserves every characteristic and every commutative unital base ring. The complex and modular consequences belong to this one target, not to separate result counts.

## 1. Exact target and conventions

For every integer m>=1 put

    N=m(m+1)/2,  B={(i,j): i,j>=1, i+j<=m+1},  G=Sym(B),
    rho=(m,m-1,...,1).

Order B lexicographically. Let E be the free abelian group with ordered basis e_1,...,e_m. Put T=E^{tensor B}; its basis words are maps a:B->{1,...,m}, denoted e_a. G acts by position permutation: g e_a=e_(a composed with g^{-1}). All regroupings of tensor factors are ordinary, without signs.

For an ordered position block D=(d_1,...,d_r), set

    alt_D = sum_(pi in S_r) sgn(pi) tensor_(k=1)^r e_(pi(k)),

with factors placed at d_k. Let R_i=((i,1),...,(i,m+1-i)) and C_j=((1,j),...,(m+1-j,j)). Define

    v_R = tensor_i alt_(R_i),    v_C = tensor_j alt_(C_j),
    z_m = v_R tensor v_R tensor v_C in T^{tensor 3}.

Let S_Z^rho be the integral Specht lattice in the word permutation lattice of content rho, with the usual row-tabloid realization. Both v_R and v_C are polytabloids in this same word realization: arrange the blocks R_i, respectively C_j, as the columns of a shape-rho tableau; the k-th position within each column has row letter k. The tabloid-to-word map is a bijection of integral bases and carries column alternation to the displayed vectors. In detail, define the tableau t_R by putting position (i,j) into tableau cell (j,i), and define t_C by putting position (i,j) into cell (i,j). Each tableau has shape rho; its columns are exactly the indicated ordered blocks. Their row words are j and i, respectively. The integral Specht lattice is, by definition, the Z-span of all polytabloids in this tabloid module, so the orbits of either t_R or t_C generate that same lattice. The inverse permutation in the position action has the same sign, giving the displayed alternations with no extra scalar. The lattice S_Z^rho is free as a subgroup of the finite free abelian group T, so its triple tensor embeds in T^{tensor 3}. Thus z_m lies in L_m=(S_Z^rho)^{tensor 3}, with diagonal G-action. This identification uses the standard integral polytabloid definition, not complex irreducibility or semisimplicity. Equivalently, take three orbit lattices Z[G]v_R, Z[G]v_R, Z[G]v_C, each an integral Specht lattice, inside the three copies of T.

**Theorem.** For every m>=1, the map

    I_m: Z[G] -> L_m,    delta_g |-> g z_m

has an explicit Z[G]-linear left inverse P_m given in §2. In particular its N! displayed images are linearly independent and generate a split regular summand over Z. For every commutative unital ring A, base change gives a split A[G]-linear embedding

    A[G] -> (S_A^rho)^{tensor 3},    delta_g |-> g z_m.

Here S_A^rho=A tensor_Z S_Z^rho; there is no restriction on the characteristic, no inversion of factorials, and no modular irreducibility assertion. In particular, over C each irreducible occurs in the tensor cube with multiplicity at least its dimension. The main claim is the explicit integral splitting, not mere complex constituent support.

## 2. The local map and the regular word lattice

Let U be free over Z on letters f_(r,a) for 1<=r<=2m-1 and 1<=a<=m. Define a local Z-linear map

    q: E tensor E tensor E -> U,
    q(e_a tensor e_b tensor e_c) = f_(a+b-1,a) if a=c,
                                  0 otherwise.

Apply q at every position, after regrouping T^{tensor 3} as (E^{tensor 3})^{tensor B}. Denote this map by q^B.

Let D={(r,a):1<=a<=r<=m}; it has N elements. Let W_D be the sublattice of U^{tensor B} spanned by words containing each letter f_(r,a), (r,a) in D, exactly once and no other letter. Let pi_D be the coordinate projection onto W_D, zero on all other basis words. It commutes with G because a position permutation preserves content. The same local map q is used at every position, so q^B is also G-equivariant.

Define a bijection w:B->D by

    w(i,j) = (m+1-i, m+2-i-j).

Indeed, row i of length r=m+1-i has second coordinates r,r-1,...,1. Let e_w be the corresponding word. The map

    J_m: Z[G] -> W_D,   delta_g |-> g e_w

is a Z[G]-module isomorphism: all letters of e_w are distinct, and its position orbit is exactly the basis of W_D. Set

    P_m = J_m^{-1} composed with pi_D composed with q^B,

restricted to L_m. All maps are given on integral bases, and no averaging or division is used.

## 3. The projection identity

We prove

    (pi_D composed with q^B)(z_m) = e_w.                 (1)

An expansion term of v_R tensor v_R tensor v_C is specified by three words a,b,c. On each row of length r, the a-labels and b-labels are separately permutations of 1,...,r. On each column of height h, the c-labels are a permutation of 1,...,h. Its coefficient is the product of their row, row and column permutation signs. Every triple of words occurs exactly once in this expansion, since the blocks are disjoint.

If q^B does not kill the term, a=c at every cell. If pi_D also retains the resulting word, put d(i,j)=a(i,j)+b(i,j)-1. Globally the retained d-labels contain each r exactly r times. Therefore

    sum_B d(i,j)^2 = sum_(r=1)^m r^3.                  (2)

On a fixed row of length r, both a and b are permutations of 1,...,r, so sum_row d=r^2. Consequently, as an identity of ordinary integers attached to this combinatorial term,

    sum_row (d-r)^2 = sum_row d^2 - r^3 >= 0.         (3)

Summing (3) over rows and using (2) gives zero. Each square in this integer sum is nonnegative, hence d=r at every cell of that row. This argument concerns the support of the fixed integer word expansion. It remains valid when coefficients are later reduced in any characteristic; it does not invoke an ordering on the base ring.

Thus every surviving term satisfies

    a=c,                  b(i,j)=m+2-i-a(i,j).         (4)

The common word a=c has the row palette 1,...,m+1-i in each row and the column palette 1,...,m+1-j in each column.

**Nested-palette lemma.** The only such word is

    a(i,j)=m+2-i-j.                                    (5)

Proof by induction on m. In the top row, its entry m can occur only in column 1, since every other column has palette maximum below m. After that position is filled, entry m-1 can occur only in column 2, since column 1 is occupied and later columns have smaller maxima. Continuing forces the top row m,m-1,...,1. Removing it removes the largest letter from every column. The remaining row and column palettes, with row index decreased by one, are exactly those of the size-(m-1) triangle. Induction proves (5), including m=1. Conversely (5) visibly has both palettes. End of lemma.

Equations (4)-(5) force b(i,j)=j. Hence exactly one expansion term survives. Its first a-row assignment is reversal on every row, its second b-row assignment is the identity, and its third c-column assignment is reversal on every column. If H=sum_(r=1)^m binom(r,2), its sign is

    (-1)^H * 1 * (-1)^H = +1.

Its output at (i,j) is f_(m+1-i,m+2-i-j), so it is e_w. This proves (1) over Z with coefficient exactly one.

## 4. Splitting and base change

Equivariance and (1) give P_m(g z_m)=delta_g for every g. Thus P_m I_m=id_(Z[G]). The standard splitting identity gives

    L_m = I_m(Z[G]) direct_sum ker(P_m).

In particular the displayed orbit is a Z-basis of its regular summand. Tensoring the maps and their identity with any commutative ring A preserves the left-inverse identity; tensor products reassociate to (S_A^rho)^{tensor 3}. No exactness or flatness assumption on A is needed for a split identity. This proves the theorem with every original all-m and all-characteristic quantifier.

## 5. Source and prior-work boundary

The source contract is pinned at OpenAI math commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, accepted true by the user. The present integral proof does not use the upstream conclusion of Saxl positivity as a premise. It uses explicitly credited constructions and supplies the integral argument here. Authentication, exact read extents, and source-contract records are in [source-manifest.json](source-manifest.json), [read-manifest.json](read-manifest.json), and [source-contracts.json](source-contracts.json).

**Inherited operations.** OpenAI's *A Cyclic Polytabloid Proof of Saxl's Conjecture*, §§2–3 (`lem:polytabloid`, `dom:pair-letter-map`, `dom:square-minimum`, `dom:noncancellation`, `dom:permutation-quotient`), supplies the ordered row/column alternating generators, the pair sum-letter operation, the squared-deficit argument, and the factorial coefficient. Its §4 `lem:sector-induction` is an antecedent for recognizing position orbits in disjoint coordinate sectors. These are inherited mechanisms, including the entire square-deficit calculation, not separate contributions of this candidate. The source works over C; the integral polytabloid identification and split identity needed here are proved above. The companion *Universal Tensor Squares for Symmetric Groups*, §1 `thm:main`, §2 `eq:block-specht` and `thm:cyclic-input`, and §5 `lem:balance-separation`, gives ordinary complex support statements and further sum-letter/coordinate separation constructions. Neither its stated main theorem nor the pinned cyclic theorem is an integral regular-summand statement. These source files were authenticated at the specified commit; no attempt was made to audit their accepted truth.

**Already-paid project deduction.** I21, *Constructive signed dominance maps, their ranks, and wider-band limits*, §2.1, already identifies the repeated-row orbit `C[G](v_R tensor v_R)` with the whole `M^rho`: the coset map followed by the source pair projection sends each coset basis vector to a different word multiplied by a fixed nonzero scalar. The scalar is

    (-1)^(sum_r binom(r,2)) product_r r!.

That scalar can be divided by over C but need not be a unit over Z or in positive characteristic. The entire complex permutation-module identification is credited to that prior project work. I21 §§1–3 were read for this boundary; its signed constructions are not new results in this submission, and its experiments were not rerun or adopted as this candidate's checks.

**Ordinary tensor cubes.** Harman–Ryba, *A tensor-cube version of the Saxl conjecture*, Algebraic Combinatorics 6 (2023), 507–511, [DOI 10.5802/alco.267](https://doi.org/10.5802/alco.267), Theorem 1.1 already proves all complex irreducible constituents occur. Their Theorem 2.4 says `M^mu tensor S^mu` contains `M^{C(mu)}`, where `C(mu)` has `i` parts of size `mu_i-mu_(i+1)`; for the staircase it is `(1^N)`, so this last module is the regular module. Together with the I21 repeated-row identification, this already yields abstract regular containment in the complex staircase cube by semisimplicity. Neither ordinary support nor ordinary regular multiplicities are advanced as new here.

**The precise modular antecedent.** Harman–Ryba §3, Lemmas 3.1–3.2, the second proof of Theorem 1.1, and Remark 3.3 establish that in characteristic 2 every projective indecomposable occurs as a direct summand of the staircase cube. This is stronger than merely observing all composition factors. It must not be described as an open or new conclusion. Their argument uses the fact that the staircase is a 2-core and hence its reduction is simple projective. In a splitting field, containing the regular module would require each projective cover P(D) with at least dim(D) copies; occurrence of each projective indecomposable alone does not state those multiplicity bounds, an explicit specified generator, a Z-splitting, or all characteristics. Bessenrodt–Bowman–Sutton, *Kronecker positivity and 2-modular representation theory*, Trans. AMS Ser. B 8 (2021), 1024–1055, [DOI 10.1090/btran/70](https://doi.org/10.1090/btran/70), introduction and §5, supplies the earlier projective-character approach and the strengthened 2-modular **square** conjecture (p. 1029). Bessenrodt–Bowman, *Splitting Kronecker squares, 2-decomposition numbers, Catalan combinatorics, and the Saxl conjecture*, [arXiv:2202.03066v3](https://arxiv.org/abs/2202.03066v3), §§1.4 and 3, supplies related projective-character identities; Theorem 3.7 is a symmetric/exterior multiplicity identity for the staircase, not a regular integral cube splitting. These exact versions and read ranges are recorded; none of these claims is inferred from a catalogue abstract.

**Inherited triangular uniqueness.** Ikenmeyer, *The Saxl conjecture and the dominance order*, Discrete Mathematics 338 (2015), 1970–1975, [arXiv:1410.6549v2](https://arxiv.org/abs/1410.6549v2), §4 defines `beta(i,j)=m+2-i-j` on the same triangle, and §5 forces this labeling uniquely from row and column alternating palettes. The nested-palette lemma above is a self-contained form of that antecedent combinatorics. The labeling and its uniqueness are not advertised as newly discovered.

**Proposed increment and limit.** The candidate combines those inherited mechanisms with the local equality filter `a=c`, retains the refined letters `(a+b-1,a)`, and projects onto one occurrence of every triangular letter. The specified tensor then maps to a single word with coefficient **+1**, rather than a factorial multiple. This yields the explicit integral retraction and every-ring base change for this tensor and all m. The independent contribution gate must decide whether this is a substantive structural advance or an explicit technical consequence of existing operations. The bounded comparison did not locate this exact integral statement in the inspected sources; that is not a literature-exhaustiveness or worldwide-priority claim. Possible general integral formulations of the inherited operations remain a question for that gate, not a claimed exclusion.

## 6. Reproducible validation and its limits

Run from this directory with Python 3, with assertions enabled:

```sh
python3 -B run_checks.py
python3 -B verify_artifacts.py
```

The first command reruns the candidate's saved original check programs and records their commands, exit codes, input hashes, output hashes and standard output in `check-run.json`. It does not use a parent implementation or an external agent. The second checks the frozen manifest and checksum coverage without modifying files.

`projection_controls.py` expands the actual three alternating layers with integer coefficients. At m=1,2,3 it independently applies each position permutation before a full monomial expansion: respectively 1, 6, 720 orbit vectors, with 1, 8, 1728 monomial triples each. Every image has one surviving term, the appropriate translated word, and coefficient +1. At m=4,5 it enumerates the two single-layer word sets and prunes only by the map's literal equality condition `a=c`; this is a matching-pruned check of the base vector, not a full orbit expansion. It finds one matching word and checks respectively 288 and 34560 second-layer choices. No palette-uniqueness or deficit lemma is supplied to the checker as a premise.

Five m=2 mutations reject the unit target identity: removing the equality filter cancels the third layer; retaining only sum and third letters gives coefficient 2, which is zero modulo 2; testing `a=b` gives zero; changing the sum shift to `a+b` gives zero; replacing the column third layer by rows gives two nonzero output words. In the last mutation the target coefficient remains 1, so a check of that coefficient alone would miss the defect. These are effective negative controls on the identity, not disproofs of any other possible construction.

`tensor_controls.py` separately computes exact complex character diagnostics at m=1 through 5 by Murnaghan–Nakayama bead moves, checks orthogonality and sign examples, and verifies multiplicities at least the irreducible dimensions. These computations have no modular or integral force. The all-m, all-ring theorem rests on §§1–4, not on either finite computation. The preserved predecessor results were actually rerun in this continuation; they are not described as independent external review.

## 7. Handoff and unresolved gates

The full target is unchanged: every m>=1, the specified `v_R tensor v_R tensor v_C`, all N! translates, a Z[G]-linear splitting, and every commutative unital ring after base change. No part is narrowed to characteristic zero, characteristic two, asymptotic m, constituent support, or a different generator.

The proof and source comparison are ready for independent full-proof and contribution review. That review should check the exact lattice identification, the position action convention, content projection equivariance, the unique surviving term and its sign, and the split base-change identity; it should separately evaluate significance against the credited prior mechanisms. The manuscript gate should also review this original prose and its attribution. No unresolved internal algebraic gap was identified in this continuation, but none of the three independent gates is marked passed. The campaign remains at the user-reported 2/10; this candidate has no accepted result number.
