# T314C independent contribution/eligibility review, round 1

Reviewer: independent contribution sub-agent (Claude Opus 5.5 via Factory). Fresh first review. This is not an acceptance decision, not a proof gate, and not a count change. The parallel reviewer's report was not opened. No nested agents, shared-ledger edits, author-packet edits, staging, commits or uploads.

## Verdict

**TECHNICAL** for the exact, unchanged T314C target (frozen scope SHA256 `676eed91…f29e`, candidate `7bc61c8a…eaea9`, author manifest `b8b77b3b…6ff4a`), assuming the full proof is correct.

- Not **SUBSTANTIAL**: the only new operation is a short combination of standard facts. Its qualitative consequences are reachable by more routine routes, as shown in §4.
- Not **DUPLICATE**: no primary body I read states the bound ell(G_beta,1) ≥ d + rho(beta), or the bound (3d−1)/2 for the finite-field family. This is a bounded-reading statement, not an absence certificate.
- Not **INELIGIBLE**: the source interface is exact (source314 `thm:main` at the pin). The target does not recycle I105 target 3, the r55/r51 excluded lanes, or the earlier poly-Z_p candidate.
- Not **BLOCKED**: every operation could be compared against read text or a complete reviewer derivation.

The correctness gate is separate. My reading of candidate §3–§4 found no defect (notes in §8), but this review certifies nothing about the proof.

## 1. Identity and inputs

The verifier `verify_review.py` requires the external SHA-256 of this directory's `MANIFEST.json` and checks it before it trusts anything else. It then checks:

- the author anchors (candidate, scope, manifest), author-packet membership, and all 34 author payload hashes (the author's preflight counted 32 at its preliminary seal; the final author manifest lists 34);
- the canonical tree `sources/preprints-tree.json` (SHA256 `eeecc1da…09b`, 13223 entries, `truncated=false`);
- the Git blob identity of all 12 copied source314 text files against that tree, with pinned raw URLs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`;
- the frozen history inputs listed in `inputs-manifest.json`;
- optionally, the private Lubotzky–Mann II body held under `/var/tmp`.

`controls.py` first verifies an unmodified copy, then runs 18 reason-checked negative controls on copies under `/var/tmp`; each must be rejected for one named reason (`control-results.json`). The controls cover a wrong or malformed anchor, edited or resealed review files, extra or missing files and directories, symlinks, changed author candidate, scope or other files (resealed or not), an extra author file, an edited canonical tree, an edited source copy, an edited frozen input, an edited private body, and self-consistent forged diagnostics caught by replay. `diagnostics.py` holds independent finite computations (§6). Hashes and finite checks certify identity and implementation only.

## 2. Exact target restated (unchanged)

For odd p, d ≥ 1 and alternating bilinear beta: L×L→L over F_p, the scope defines G_beta on (Z/p²)^d with x*y = x+y+i(beta(x̄,ȳ)/2). It claims the following:

- G_beta is powerful, of exponent p² and order p^(2d), with sectional rank exactly d.
- For every subnormal cyclic chain, ell(G_beta,1) ≥ d + rho, where rho = ½ min over nonzero f of rank(f∘beta).
- For L = F_(p^d) with odd d ≥ 3 and beta(x,y) = x y^p − x^p y, the group satisfies Z = G^p = Phi = [G,G] = pR, and ell ≥ (3d−1)/2.
- Through source314 `thm:main`, r_h(G,1) ≥ (3d−1)/2 for every h ≥ 0, and for each integer 0 ≤ t < (3d−1)/2 there is a finite p-local genuine witness.

The review keeps the whole scope. It does not narrow to restricted series or to small examples.

## 3. Credit already due in full (not counted as new)

| Input | What it supplies to T314C | Read extent |
|---|---|---|
| source314 `thm:main`, `eq:def-loss`, sharpness sentence (01-introduction) | The entire chromatic conversion r_h = ell at all heights including h = 0, and the existential witnesses | 01 and 02 read in full |
| de las Heras–Traustason arXiv:2006.12593v1 §6 | Type-(2,…,2) powerful groups; the pth-power identification G/G^p ≅ G^p; the alternating-algebra correspondence for powerful subgroups (Lemma 6.3 – Cor 6.10); Jordan–Hölder for powerful composition series | Lines 1–140 and 704–883 of the author's private text (§1 and §6 in full) |
| Gow–Quinlan arXiv:0709.0741v1, Lemmas 1–3, Theorem 1 | The exact forms Tr(b(x σ(y) − σ(x) y)), the radical equation, and constant rank n − n/(2r+1), equal to n − 1 when σ generates | Lines 1–153 and 205–242 |
| Kuhn–Lloyd arXiv:2008.00330 (retrieved v2), Defs 2.5–2.6, §5 Examples 5.12–5.15 | r_−/r_+, unbounded *relative* gaps (dihedral, noncentral H), failure of product additivity | Lines 286–465 and 1640–1889 read; §5 was read by the author |
| Classical facts | Frattini/Burnside basis theorem, symplectic maximal-isotropic dimension, trace duality, cyclic F_(p^d)^* | — |
| **Lubotzky–Mann (not credited by the author)** | d(H) ≤ d(G) for every subgroup H of a finite powerful p-group, p odd. This *is* "sectional rank = d(G)" for powerful groups. | Statement (1.1) of LM II, J. Algebra 105 (1987) 506–515, citing [LM I, 1.12]; LM I body not read |

## 4. Operation-by-operation comparison

| Candidate operation | Status |
|---|---|
| §1 Cocycle construction, x^m = mx, commutator = i∘beta, powerful, Frattini = pR | Routine, and contained in dlHT §6 (structure of the class 𝒫 through [a,b] = c^p). Concrete realization only. |
| §2 Subgroup data (U,W), \|H\| = p^(dim U + dim W), d(H) ≤ dim W ≤ d, sectional rank d | Specialization of Lubotzky–Mann d(H) ≤ d(G) for powerful groups. The (U,W) bookkeeping is elementary. |
| §3a Each order-p² factor K◁H adds a fresh projected direction (otherwise g = kz and g^p = k^p ∈ K) | One-line consequence of the pth-power map factoring through G/Z0. It has the same shape as source314's own `lem:product-series` (05-profinite, lines ~355–430): count the steps of an *arbitrary* cyclic chain that raise a rank invariant, then delete repetitions. |
| §3b At the *last* order-p² step, H/K cyclic ⇒ [H,H] ≤ K ⇒ beta(U_H,U_H) ⊆ W_K, a proper subspace | Standard: a cyclic top quotient forces the derived subgroup into K. The new choice is to apply it at the last order-p² step. |
| §3c Isotropy bound dim U_H ≤ d − rho, so s ≤ d − rho and k = 2d − s ≥ d + rho | Classical maximal-isotropic dimension. The same isotropy pattern underlies Kuhn–Lloyd's unproved remark that r_+(Ẽ_2r, W_r) = r+1 "isn't hard to check" (§2.2.2, with §8.1 identifying maximal elementary abelian subgroups with maximal isotropic subspaces). My reconstruction of that check uses exactly "cyclic C4 step ⇒ commutator containment ⇒ isotropy contradiction". This is a cognate pattern, not a statement of T314C's bound. |
| §4 Constant rank d − 1, common radical 0, span = L, Z = G^p = Phi = [G,G] | The rank is Gow–Quinlan Lemma 3 / Theorem 1 verbatim, with σ = Frobenius. The rest is routine. |
| §5 r_h ≥ (3d−1)/2 and the witnesses | Direct application of source314. No new operation. |

**Net new operation:** a roughly ten-line argument (§3a–§3c) giving ell ≥ d + rho for arbitrary cyclic subnormal chains in type-(2,…,2) powerful groups. Credit is due for handling *arbitrary* chains with mixed order-p and order-p² steps and non-powerful intermediate subgroups. dlHT handles only chains of powerful subgroups (Cor 6.10). The handling consists of choosing the last order-p² step and applying three textbook facts there.

### 4.1 Routine comparators for the advertised phenomena (reviewer derivations, complete)

These comparators test whether the *qualitative* consequences need T314C's operation. They are not literature-priority claims. They are not substitutes for T314C, and they do not narrow it.

**(a) Exponent-p comparator, same Gow–Quinlan forms, no chain argument.** Let E_beta = L × L with (x,a)(y,b) = (x+y, a+b+beta(x,y)/2), for the same finite-field beta, p odd, n = dim L odd ≥ 3.

- E_beta has exponent p and order p^(2n), so every cyclic factor has order p and ell(E_beta,1) = 2n trivially. Its rank is d(E_beta) = r_−(E_beta,1) = n.
- For H ≤ E_beta with image U and W = H ∩ (0×L), we have Phi(H) = [H,H] = span beta(U,U). So d(H) = dim U + dim W − dim span beta(U,U), and the sectional rank is n + max_U (dim U − dim span beta(U,U)).
- If dim U ≥ 2, the span is nonzero, because beta(x,xz) = x^(p+1)(z^p − z). If the span is proper, U is isotropic for a rank-(n−1) form, so dim U ≤ (n+1)/2. Hence the sectional rank is at most (3n−1)/2.
- Therefore ell − (sectional rank) ≥ (n+1)/2, which exceeds T314C's (d−1)/2 at the same dimension, and ell − r_− = n.
- Exact enumeration gives sectional rank n+1 (excess n−1) at (p,n) = (3,3), (3,5) and (5,3). At (3,3), an independent BFS over all 3955 subgroups confirms ell = 6 and sectional rank 4.

So unbounded, linear excess of cyclic length (hence of r_h) over sectional rank and over r_− at H = 1, for each fixed odd prime, is elementary once one leaves powerful groups. T314C's real distinction is that its groups are **powerful**, so r_− = d(G) = sectional rank (Lubotzky–Mann), and the excess is measured against that common value.

**(b) Powerful comparator at fixed rank 3, unbounded excess.** Let p be odd and Γ = ker(SL_2(Z_p) → SL_2(F_p)), and put P_k = Γ/Γ(p^k).

- P_k is powerful, with d(P_k) = 3 = sectional rank (Lubotzky–Mann). This uses the standard uniformity of Γ for odd p; Dixon–du Sautoy–Mann–Segal Ch. 5 is the standard reference, not re-read here.
- Suppose ell(P_k,1) ≤ l for all k. The compactness argument in the first half of source314's `lem:product-series` proof gives a closed subnormal series of Γ with procyclic, hence abelian, factors. Then Γ would be solvable.
- But Γ contains the matrices [[1,p],[0,1]] and [[1,0],[p,1]], which generate a free group (Sanov-type ping-pong, |p| ≥ 2). So ell(P_k,1) → ∞, and by source314, r_h(P_k,1) → ∞ at fixed sectional rank 3.

This gives no rate, and the exponent grows. So unbounded excess for *powerful* groups at a fixed odd prime is also reachable by routine means. What remains distinctive to T314C is **bounded exponent p², class two, and an explicit linear rate** (ratio (3d−1)/(2d) → 3/2 against d(G)).

**(c) Method ceiling.** Alternating forms have even rank, so rho ≤ ⌊d/2⌋, and the bound d + rho can never exceed (3d−1)/2 for odd d. Gow–Quinlan's n-dimensional constant-rank-(n−1) spaces are therefore extremal for this method. The finite-field family realizes the method's ceiling by inserting the classical extremal object. No further idea is involved.

**(d) Character-degree reading.** For a nontrivial λ on Z0 corresponding to f, the standard class-two computation gives χ(1)² = p^(rank B_f) for every χ over λ. So rho = min{log_p χ(1) : Z0 ⊄ ker χ}. At (3,3) the degree count 27·1 + 26·3·3² = 729 checks this. The bound is therefore ell ≥ d(G) + (minimal degree exponent over Ω₁-nontrivial characters). I found no character-degree theorem for cyclic-chain length in the material read. The generic degree-growth bound along a cyclic chain gives only trivial estimates, so T314C does not reduce to it. This reformulation is equivalent and earns no credit.

**(e) Why the chromatic consequence is still worth recording.** Kuhn–Lloyd §9.2 explains that their RP(ω)/L_p(ω) constructions cannot prove more than r_− + 1. The linear lower bound on r_h here therefore comes entirely from source314's r_h = ell. That credit belongs to source314, not to T314C.

### 4.2 Why TECHNICAL rather than SUBSTANTIAL

1. Every deep input is prior work: source314 (chromatic content), Gow–Quinlan (constant rank), dlHT (group/algebra framework), Lubotzky–Mann (sectional rank).
2. The new operation is a single-step application of three standard facts. The arbitrary-chain counting pattern already appears in the stipulated source itself (`lem:product-series`), and the isotropy pattern in Kuhn–Lloyd's extraspecial computation.
3. The headline phenomena are not new to this operation. Unbounded excess over sectional rank and over r_− at H = 1 and fixed p follows trivially from exponent-p groups, even with larger excess. Unbounded excess for powerful groups at fixed p and fixed rank follows from p-adic congruence quotients.
4. What remains is a bounded-exponent quantitative refinement whose constant equals the method's ceiling, reached by plugging in an extremal classical object. That is a clean technical note, consistent with how the campaign treated earlier source314-family work (poly-Z_p: TECHNICAL).

Upgrade routes that would change this analysis are not required here and are not claimed. Examples: an exact ell for the family, or a matching upper bound; a classification of ell for all of 𝒫 in terms of beta; or bounded-exponent powerful families with ratio above 3/2.

## 5. Required objections (must hold for any use of this verdict)

- **R1. No count.** The unchanged T314C package is TECHNICAL and must not be counted as a substantial result, even if the separate proof gate passes. No narrowed or relabelled substitute should be counted either.
- **R2. Lubotzky–Mann credit.** Scope and candidate §2 present "sectional rank exactly d" with its own proof and without citation. It is the specialization of d(H) ≤ d(G) for powerful p-groups (LM I Thm 1.12, as restated in LM II (1.1)), together with Z0 ≅ C_p^d. Any retained write-up must cite it and must not list §2 as a contribution component.
- **R3. Correct the absolute-gap framing.** comparison.md item 4 distinguishes T314C by "H=1, every fixed odd prime … with a linear quantitative excess". Any retained comparison must state two things. First, at H = 1 and fixed odd p, linear excess of ell over sectional rank and over r_− holds trivially for exponent-p class-two groups built from the same forms (§4.1a). Second, unbounded excess for powerful groups at fixed rank follows from SL_2(Z_p) congruence quotients (§4.1b). The distinguishing content must be stated narrowly: the arbitrary-chain bound ell ≥ d + rho on type-(2,…,2) powerful groups, and its bounded-exponent linear family. The sentence "the excess over sectional rank is at least (d−1)/2 for each fixed odd prime" may remain as a true consequence, not as a novelty claim.
- **R4. Gates remain separate.** This review does not certify §3–§5, the finite diagnostics, or source truth. Proof review, manuscript and formal gates are independent.

## 6. Optional credit changes (recommended, not required)

- **O1.** Cite source314 `lem:product-series` (05-profinite) as the nearest in-source operation for counting steps of an arbitrary cyclic chain that raise an invariant. The author read only 05-profinite lines 1–38.
- **O2.** Cite Kuhn–Lloyd §2.2.2 and §8.1 (r_+(Ẽ_2r,W_r) = r+1; maximal isotropic subspaces) as the cognate isotropy-in-cyclic-chain computation.
- **O3.** Cite Kuhn–Lloyd §9.2 (representation-theoretic constructions capped at r_− + 1) to explain why the linear r_h bound rests on source314.
- **O4.** Record the character-degree form of rho (§4.1d) and the method ceiling rho ≤ ⌊d/2⌋ with Gow–Quinlan extremality (§4.1c).
- **O5.** Relate the s = d case of §3 to dlHT Cor 6.10. A chain whose factors all have order p² forces beta(L,L) ⊆ W_K ≠ L at its last step, which is the obstruction to powerful solvability seen from arbitrary chains.

## 7. History screen (bounded)

- **discovery-r66-parent/chain-obstruction.md** (SHA256 `e04fab09…`), read in full. It contains the same §3 argument as author collaboration and is not a review. source-reading.json was also read.
- **poly-Z_p** (poly-zp-parent dispositions), read. This is an earlier source314-family candidate on subgroup congruences, classified TECHNICAL. It uses a different operation (GRV orbit products), so T314C does not duplicate it.
- **I105**, lines 1–38. Target 3 (explicit cell bounds) is untouched by T314C, which asserts no cell bound. It is neither solved nor weakened.
- **r64 catalogue-survey**: term search only, item 314 entry. r55/r51 exclusions are taken from the author's record and were not re-read.
- **NEW-TEN** ledger: acceptance rules (lines 1–80) and term searches. AGENTS.md and VALIDATION.md were read.
- **Not opened:** the parallel reviewer's outputs, and t314c-parent proof-r1 brief/dispatch.

## 8. Correctness notes (informational only; proof gate is separate)

- §3: U and W are monotone along the chain. dim U_H ≥ s because all order-p² steps precede or equal the last one. W_K is proper because dim W_H = dim W_K + 1 ≤ d. The commutators of H lie in K ∩ Z0 = i(W_K). The isotropy bound applies to B_f for any f ⊥ W_K. No gap was found.
- §4: (ax)^(p^(d−1)) = a x^p is equivalent, through Frobenius, to x^(p²−1) = a^(1−p), with gcd(p²−1, p^d−1) = p−1 for odd d. The trace pairing is nondegenerate even when p | d. These match Gow–Quinlan Lemma 3.
- Independent finite checks (`diagnostics.py`) found:
  - rank d−1 for all nonzero functionals at (p,d) = (3,3), (3,5), (5,3), (7,3);
  - for G_(3,3): ell = 4 (equal to the bound) and sectional rank 3 by exhaustive BFS over 364 subgroups;
  - abelian comparator: ell = 3;
  - exponent-p comparator: ell = 6, sectional rank 4.
  - Checker negative controls: a truncated rank routine is detected; BFS without normality gives a different length (3); a degenerate beta has min rank 0.

## 9. Reading and search limits (honest)

- **source314:** 01-introduction and 02-background read in full; 05-profinite lines 1–60 and 300–430 read; 03, 04, 06 and 07 only term-searched for ell/rank/example. Source truth is stipulated.
- **Primary bodies:** extents as in §3; the author's private extractions were used.
- **Lubotzky–Mann:** LM II downloaded privately (`/var/tmp/t314c-contribution-r1/private/lubotzky-mann-II.pdf`, SHA256 `fb614317…2af9`); its opening and §1 statements were read. LM I and the DDMS book were not read; their theorem numbers are as cited by LM II or by standard knowledge.
- **Web searches (bounded, 8 queries):** cyclic subnormal-series length, polycyclic length, LM rank theorem, powerful/alternating/isotropic, blue-shift r_+ follow-ups, and chromatic Smith examples. Hits were mostly irrelevant textbooks and notes. One lead, the ResearchGate survey "Group Actions and Chromatic Homotopy Theory" (2026-09-26), was not accessed. Wikipedia "Powerful p-group" was consulted as a secondary confirmation of rank = d(G).
- **Absence claims:** none. Absence of hits is not evidence of novelty or of priority.

Third-party bodies remain private (author `private/` is git-ignored; LM II is outside the repository) and are not relicensed.
