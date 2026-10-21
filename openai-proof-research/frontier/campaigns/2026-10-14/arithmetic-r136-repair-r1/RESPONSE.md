# T054L136 — first substantive author response

**Outcome: UNRESOLVED_FULL_SCOPE_REPAIR.** This is research and response to both completed first-round reviews, not another review, a replacement statement, or a request for a particular assessment. The ENTIRE frozen statement is retained byte-for-byte in FROZEN.md, SHA256 `cde199a706104ed0db542704b0470d451ce5e11bd7ff0cc74d62df68130b4a77`. The unchanged original author proof, SHA256 `6c9ea784ead7d96835a69a3a41d15f89ec3a13ac4faa83b342a6adcc76c53446`, was copied privately and never edited. The claim in that proof that every frozen quantifier is proved is withdrawn. No complete REVISED-PROOF.md is supplied because the full argument remains open.

The two supplied reviews are treated as objections and navigation. The actual original proof, exact named reading/limits records, Source054 canonical main and relevant passages in all seven operative includes, and the needed primary/history passages were read directly. The operative source revision and its proofs are stipulated, not re-audited. Exact own reading extents and unexpanded dependencies are in private/READING.md; the reviews' full reading claims are not inherited.

## A. What this repair establishes

DERIVATIONS.md contains seven detailed sections. In addition to correcting the sign and retaining the 3-adic and norm-2 arguments, it establishes the following auxiliary facts.

1. **Exact minimum of the original diagonal lattice.** For every a≥1, μ(N_a)=2a, without either arithmetic witness condition. An explicit integral isometry gives a descent in the positive first coordinate. This confirms that the obstruction lies in other global classes of the genus, not in bounding the initially constructed N_a.
2. **An entire symbolic companion family.** If z is positive and even and a=6z²+4z+1, the two primitive norm identities for a and a+1 force every odd prime of a(a+1) to split in Q(√−2). Unit-line matching works even at higher valuations. Together with the review's symbolic 2-adic basis this proves q(N_a)=q(<4>⊥<−a(a+1)>).
3. **Infinitely many allowed a at FIXED B=22 with minimum 4 companions.** Starting with a=42673=139·307, a+1=2·19·1123, the Pell matrix [[17,72],[4,17]] preserves x²−18w²=59401. A power equal to the identity modulo 6·199·139²·307²·19² produces an unbounded sequence a_j=199²+12w_j², all with prime divisors 1 modulo 3 and all frozen witnesses through 22. The companion has μ=4 exactly. Primitive gluing and period realization make it an actual same-integral-T projective K3 complement for every exact-A cubic with this parameter and scalar End. The discriminants tend to infinity.
4. **Why discriminant alone cannot substitute.** The norm-4 class can be made ample and is base point free, giving genus-3 pencils. Its third multiple is very ample of square 36 and Hilbert polynomial 18m²+2. These companions belong to a single bounded projective family despite unbounded discriminants. This is a counterargument to a general determinant-based bounded-family exclusion, not a claim that these particular K3 surfaces occur in the source's marked diagram families.
5. **The limit of a stronger arbitrary-B CRT attempt.** For every B one can choose all a-primes to split in both Q(√−2) and Q(√−3), excepting the squareclasses 2 and 3 from the (i) construction and handling both with q≡19 mod24 in (ii). CRT also forces a≡1 mod16. The resulting allowed parameters have norm-4 local solubility at 2, 3, every a-prime, and all selected a+1 witnesses. The unselected primes of a+1 remain uncontrolled. This is NOT an all-prime solution or an unbounded-B auxiliary counterexample.

The fixed-B Pell sequence does not turn B=22 into B→∞. The arbitrary-B CRT sequence does not turn a finite witness list into full prime-support control. Neither is a theorem counterexample or a proof of rationality. These distinctions are part of the mathematical result of this response.

## B. Response to correctness r1, section by section

### C1 — sign, P1, and the diagnostic

Agreed. At p|a+1 the equation is −x²=n modulo p. Frozen(ii) supplies the wrong sign when p≡3 mod4; then the equation is locally soluble, including over Z_p by Hensel. I do not change (ii), impose a residue class on its primes, or restrict to the author's q≡5 mod12 construction. The old local-calculation.py was read, never run against its old output path. Its positive-square residual is not reused.

The parent's a=133,n=3 calculation is a valid test of the bad modular step. It is not a global norm-6 example: at 3 the form x²+y² is anisotropic modulo 3 and represented nonzero half-norms have even 3-adic valuation. This observation is retained for all complements by genus equivalence. It does not exclude n=2 or n=5.

### C2 — all-complement counterexample and the unknown threshold

Agreed. The a=18961,B=4 example satisfies the frozen hypotheses and its <4>⊥<−359538482> companion has the same genus. The supplied 2-adic basis is retained as a symbolic identity, not as finite residue evidence. The new derivation extends its use to all even z in §A.2, then constructs an infinite fixed-B family in §A.3.

The requirement that the complement occur for the same integral T is substantive. Gluing M to T along the anti-isometry, using the unique even unimodular lattice of signature (3,19), retaining the original Hodge line, and applying period surjectivity realizes the companion. Primitivity and absence of rational (1,1) vectors in T give NS exactly M. The positive-square class gives projectivity. Scalar End transports. Thus none of these companions can be omitted on a realizability pretext.

This refutes the old auxiliary lemma without any B-threshold, and refutes determinant growth as a general substitute. It still does not refute an eventual bound as B→∞. No assertion is made about the diagnostic a=76513 beyond the bounded information in the completed review; that number is not needed for this response.

### C3 — discriminant transport, anisotropy, rank-20 centers

These interfaces are retained. At valuation-one odd primes, the discriminant form determines the modular line and the determinant determines the unit line. This is local equivalence, not global isometry; the exact diagonal minimum in DERIVATIONS §6 illustrates why those notions must stay separate. At 3, unimodular binary classification or the full genus theorem supplies the transport.

D=4a(a+1) is nonsquare, so every binary complement is anisotropic. For a whole surface center with p_g=1, rank T=20, and determinant D, minimalization gives b₂=22−8q−K² and ρ=2−8q−K²≥1. Hence q=0, K²=0 or 1. The K²=1 case has rank-one NS generated by the canonical class of square one, giving |disc T|=1 by unimodularity, a contradiction. The elliptic K²=0 case has an isotropic divisor and square absolute discriminant, also a contradiction. The remaining minimal surface is K3. This uses the whole T-block and the classical surface operations, not Kulikov's conjectural decomposition assertions or a rank-22 conclusion at rank 20.

### C4 — finite-order automorphisms

Retained with a corrected premise: **norm 2 is independently excluded** because n=1 cannot use (ii), and (i) works. This applies to every complement, without a large-minimum assumption.

For a finite-order g, the scalar action on T and the positive invariant ample direction in rank-two NS imply g² acts identically on H². Finite-order cohomological faithfulness makes g an involution. Primitive eigensublattices of a unimodular lattice have 2-elementary discriminant groups, by projecting integral representatives of dual functionals using (1±g)/2. A nontrivial symplectic case would have a negative rank-one <-2> anti-invariant lattice, impossible because one root sign is effective. In the nonsymplectic case a rank-one invariant lattice would be <2>, now independently excluded; a rank-two invariant lattice is all NS and would have discriminant at most 4. Thus no nonidentity finite-order automorphism occurs.

The downstream uses are exactly the quadratic small orbit, the degree-two component extension L/K, and the complementary-orientation involution. Their absolute extension degrees need not be two. No arbitrary infinite-order exclusion is imported from pre:small-orbits. Geiser and Bertini involutions are on the link's del Pezzo middle surface. Derived partners are not assumed to share full automorphism groups.

### C5 — uniform boundedness and pencils

The conditional extension is retained, not promoted to an unconditional assertion. In an anisotropic K3 lattice a moving pencil class C₀ is positive. The identities C₀²=Σm_i² and 2g−2=Σm_i give 2g−2≥√(C₀²). A bounded smooth model gives a pushforward ample D with D²≤A²+(A·K)². These are precisely positive-square estimates. The source's Hilbert schemes of bounded free rational curves reduce bounded threefold MRC bases to the same surface estimate.

The four exclusions remain distinct: bounded varieties; bounded-degree covers with bounded marked branch support; surface fields over curves with bounded geometric fibre genera; and threefolds over curves with bounded uniruled geometric surface fibres. Stein factorization and the non-uniruledness of K3 surfaces handle the latter two without bounding the entire space over the curve. Determinants alone prove none of these exclusions, as the fixed-B family demonstrates.

The order of choices remains ordinary fourfold diagrams, then one c with 0<c<1/4, then the log threefold and discrepancy≤1 extraction families, then the maximum of finitely many square/genus thresholds. These choices are independent of a, X, all complements, the test subcollection, factorization length, and resolving start. The unpaid step is making every allowed all-T test collection exceed those bounds for all sufficiently large B.

### C6 — actual Galois sets, embedded fields, endpoints

Retained as a single compatible conditional mechanism. The five-/three-element pencil sets and eight-element orientation sets keep coefficient one per orbit field. The degree-six comparison identifies actual triples through the C₃/S₃ quotient, not arbitrary Gassmann-equivalent representations. The (9,4) case uses stars and complementary triangles. The nontrivial conic move has r=8−K_W²≤7; structured isomorphisms need no such bound.

Residues and their quadratic/orientation covers are formed over the original fields and their supports are retained under geometric base extension. The residue-complex/purity argument bounds the branch locus and field-factor degrees by fourteen. The first-departure proof compares every eligible embedded subfield, including a zero candidate. It obtains any required curve-field inclusion from the incoming endpoint. At an arbitrary conic end it does not assume C(Q)⊂k: the negative program first runs over the conic base, bounds surviving discrepancy≤1 extractions, then runs over Q and compares outputs in the absolute geography. Both the first-departure and final-endpoint alternatives are kept. Subject to the exclusions, these operations yield c_u=Δ(v+s) and endpoint vanishing. They do not yield that vanishing without those exclusions.

### C7 — cubic/K3 and whole-block evaluation

Retained. d=2a is admissible; K=<H,σ> is primitive. The stipulated associated-K3 integral isometry gives <h,t'>=N_a inside NS(S₀). The exact rank, primitive complements, and determinant D make its index one. Equality of rational Hodge structures or determinants alone would be insufficient, and neither is substituted.

BLMPNS Corollary 29.7 is the every-cubic untwisted assertion. The hyperbolic-plane pairing in Proposition 33.1/Lemma 33.2 gives a universal family and trivial Brauer class. The categorical K3 need not be S₀. The test still contains all projective K3 surfaces with the prescribed integral T.

Under a hypothetical rational factorization the stipulated gw:blowup and gw:blocks cancel entire saturated integral center blocks. The one-dimensional (3,1) part leaves one net block; the rank-20 classification above identifies exactly all centers counted by u. Thus the conditional c_u=1 evaluation survives. Restricting u to the diagonal N_a surface would not be justified by this block count. The missing contradiction is still the universal c_u=0 evaluation.

### C8 — locus, genericity, infinitude, history

Retained independently of the failed minimum assertion. H is characteristic of square three; H-perpendicular has diagonal squares 6a,2(a+1). Completing the square in A_a shows no norm-two vector. Rank plus discriminant length is at most six. The actual Yang–Yu Theorem 5.1 and embedding/orbit assembly therefore apply to the full primitive-embedding locus, giving nonempty irreducible closed algebraic dimension 18 inside smooth cubic moduli. At a very general point, extra rational Hodge vectors and nonscalar rational endomorphisms lie in countably many proper algebraic Hodge loci; the period quadric is not contained in a union of proper eigenspaces. This gives exact A and scalar End, but their irrationality remains open here.

For fixed B, the original character construction for all n outside 3 times squares, followed by q≡5 mod12 and CRT/Dirichlet for ell, proves infinitely many allowed a. It does not cover the entire allowed family for irrationality. Distinct determinants and the very-general exact lattice distinguish the entire loci. The additional labelling calculation det<H,u>=2ay²+6(a+1)z²≥2a is retained and does not bound other K3 complements.

The actual i05 §3 already contains the −3 character compatibility issue. The actual Arithmetic34 §5 contains a negative-square modular argument for Lucas/golden-ratio norms, not a K3 theorem or the same −3 calculation. Those sections were read at their original byte intervals. No older scope was reopened.

### C9 — every frozen quantifier

One existential B₀, every B≥B₀, every allowed a, every exact-A cubic with scalar End, and every actual same-T K3 complement all remain in the target. Neither review example, nor the new fixed-B infinite sequence, resolves that eventual universal assertion. The untwisted category, locus, genericity, infinitude and distinction arguments remain available at their stated scopes. Universal irrationality and its very-general consequence remain unproved. There is no narrowed substitute.

## C. Response to contribution r1, section by section

**K1, input status and reading.** The frozen statement/proof identities and stipulated pin remain fixed. Own fixture authentication uses the complete nontruncated tree and exact primary bytes. I did not read Hassett's unavailable original association proof or repeat the reviewers' retrieval attempts; the integral association interface is explicitly the stipulated cub:associated. Own limits are disclosed, not replaced by the reviewers' broader reading lists.

**K2.1–K2.6, the strongest compatible payment.** I accept the proposed conditional reconstruction: classical gluing and rank-20 classification; the finite-involution test; the whole-block count; the simultaneous bounded-MRC and pencil exclusions; actual surface-link Galois sets; marked covers and intrinsic embedded-subfield correction compose once the uniform all-complement positive-square interface is supplied. Sections B3–B7 retain the exact common hypotheses and order of constants. This response adds no claim that one of those geometric operations becomes a new contribution merely because the rank changes.

A weaker sufficient interface than E(B,a) is worth distinguishing. For every fixed C, one could prove that all allowed parameters at all sufficiently large B have μ(M)>C in EVERY same-T complement. After choosing the finite geometric threshold C, that divergence would suffice. It is not proved here. The original proportional bound μ>2B is not the only possible repair, but a growing discriminant is not such a weaker interface.

**K3, categorical and locus conclusions.** Their full every-cubic and full-locus quantifiers are retained, with the exact integral Hodge versus categorical distinction, Yang–Yu primitive embedding and orbit operations, and algebraic exceptional sets. These conclusions alone do not prove the frozen irrationality clause.

**K4, infinitude and overlaps.** The existing CRT/Dirichlet argument is already paid and remains valid at every fixed B. The new arbitrary-B compatibility calculation is also an elementary character/CRT composition and is not asserted to establish new mathematical contribution. The old i05/Arithmetic34 scopes stay unchanged. Lin–Shinder's general unbounded center-invariant construction does not replace the missing source exclusions; elliptic rank-20 p_g=1 centers would have square discriminant and are excluded by the same classification. No generic unboundedness assertion has been substituted for the needed all-complement property.

**K5, the a=469 certificate.** Agreed in full. The odd-primary multipliers (1,3,18,14) at (5,7,47,67), and the identity on Z/2⊕Z/4, give q_<938,-940>=q_<10,-88172>. The exact numerator congruences in Q/2Z, determinants and all twenty witnesses are checked by the repair's independent read-only mathematics script. Gluing realizes the norm-10 lattice for the same T. It is a failure of E(20,469), not proof of rationality or a contradiction beyond unknown B₀. The same treatment applies to the separate correctness example.

**K6, contribution and full scope.** There is no closed full-scope residual operation to point to, and no complete compatible proof of the unchanged theorem. Difficulty of the remaining arithmetic is not evidence of contribution. This response does not assign correctness, contribution, acceptance, or count and does not request a retry or a particular grade. Parent alone integrates any subsequent work.

## D. Change map from the unchanged author proof

| Original location | Response disposition |
|---|---|
| §1 | Keep conventions, integral whole-block premise, and sign of c_u. |
| §2 | Keep only as a CONDITIONAL test extension, with all three hypotheses and uniform choice order explicit. |
| §3, negative-square calculation | Correct the a+1 sign; withdraw the asserted universal μ>2B implication. Retain odd-prime transport and nonsquare anisotropy; add the valid 3-adic and n=1 deductions. |
| §3, global minimum | DERIVATIONS §6 proves μ(N_a)=2a for the diagonal lattice; §§2–4 explain why it cannot be transported to its entire genus. |
| §4.1 | Keep rank-20 whole-center classification, including both numerical exclusions. |
| §4.2 | Keep finite-order exclusion; supply no-square-2 directly from frozen(i) at n=1. |
| §5, collection and c_u=1 | Keep the integral associated-K3 and index-one argument, all same-T centers, and the hypothetical rationality block evaluation. |
| §5, application of §2 / c_u=0 | Remains unproved. Do not state the irrationality contradiction. |
| §6 | Keep locus and genericity; remove any unconditional inference of irrationality from them. |
| §7 | Keep infinitude; withdraw its final assertion that all frozen quantifiers have been proved. The constructed stronger subfamily is not the full target. |
| §8 | Replace the implied closed arithmetic operation by the explicit outstanding obligation. No contribution claim. |
| §9 | Keep the additional labelling bound and distinction between associated and categorical K3 surfaces. |
| local-calculation.py | Do not reuse its erroneous residual or execute its old writer. Own checks use negative squares on both branches. |

UNRESOLVED.md specifies the exact remaining mathematical operation. DERIVATIONS.md is durable partial research, not a revised proof of FROZEN.md. The sealed packet is an artifact handoff only.
