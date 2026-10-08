# H017 information mechanisms: raw Factory Opus report

Unverified initial output, retained for independent review. No claim below changes the accepted ECDLP baseline without mathematical, source and complete-cost verification.

I have three new mechanisms, two exact pruning facts, and a short list of routes I checked and dropped. None of this shows a speedup, so verified improvement is still NONE. I expect all three mechanisms to fail, but each one leads to a known recovery algorithm, and each can be tested cheaply and decisively.

**Scope.** This was read-only work. I wrote no files, ran no experiments and started no child agents. I checked STATE, RESEARCH_LOOP, the H016 shortlist and these earlier records: H002 learning cards, H003 noisy recovery and orbit invariants, H005, H006 decoding, H009, H013 MCL, group-action, coordinate and hybrid cards, H014, H015, and H016. I cite the literature from memory and did not re-read it this session, so treat novelty as unestablished.

## Two exact facts behind the cards

**Fact A: F_p-valued linear recurrences hit the embedding-degree barrier.** Take any feature f with values in F_p, and look at the sequence s_n = f(nG). It repeats with period q. Its minimal polynomial divides X^q − 1 = (X−1)·Phi_q(X). Over F_p, Phi_q splits into irreducible factors of degree e = ord_q(p), which is the embedding degree. So any non-constant sequence of this kind has linear complexity of at least e, which is usually about q. This one argument rules out several routes:
- F_p-linear-recurrence or Berlekamp–Massey style ideas.
- Miller-value products. By Weil reciprocity they depend on the integer representative of n, so they are not functions of Q.
- Kummer and descent maps for ℓ = q.
- Cross-characteristic homomorphisms built from E over F_p.

Over F_q the picture changes. There X^q − 1 = (X−1)^q, and X^(q−1) − 1 splits into distinct linear factors. Low linear complexity is then exactly a polynomial or sparse structure in the log, with no barrier. Cards 1 and 2 use this route.

**Fact B: relational ("siamese") learning is no stronger than single-point learning.** Suppose a predictor A(R1, R2) targets a label that depends only on log(R2 − R1). Set B(D) = A(R, R + D), with R uniform and freshly sampled. This costs one addition and one random point, and B matches A's accuracy. Under rerandomization, R1 carries no information about the label. So every learned component has to end in one of four bridges:
- a scalar predicate (the H003/MCL route);
- a label-tracking map that concentrates collisions (H009, or Card 3 here);
- a decomposition oracle (L4);
- a polynomial or sparse structure in the log (Cards 1 and 2).

## Card 1: exact sparse structure in the log, found by Berlekamp–Massey on geometric orbits

- **Mechanism.** Use mixed-modulus features with values in F_q: X̄ = centered integer representative of x, reduced mod q; Ȳ the same for y; the H016 quantity kappa mod q; and the formal parameter centered(−x/y) mod q.
  - Certify a primitive root w mod q. Then compute s_i = f([w^i]G) for i < 2T.
  - Run Berlekamp–Massey (BM) over F_q. If the linear complexity is t ≤ T, then f(nG) = sum over j ≤ t of c_j·n^(e_j) on F_q^*. In the language of Ben-Or–Tiwari, the BM roots are w^(e_j).
  - Dense polynomials of degree L are (L+1)-sparse, so this test covers them too.
- **Recovery.** Compute f([w^i]Q) for i < t. Those values satisfy the same recurrence, with coefficients d_j = c_j·k^(e_j). Solve the transposed Vandermonde system, then form k^(e_j) = d_j/c_j.
  - If some e_j = 1, k follows directly.
  - Otherwise, get each e_j from w^(e_j) with a discrete log in F_q^*. That costs L_q(1/3), or Pohlig–Hellman if the synthetic family declares q−1 smooth. Charge it either way.
  - Finish by verifying kG = Q.
- **Work and memory.** About 2T + t scalar multiplications, plus BM at O(T^2) (or quasi-linear), plus the solve, root and log steps. Memory is O(T). Setup is factoring q−1 and certifying w. That beats sqrt(q) if t ≤ q^(1/2 − ε).
- **Training and generalization.** There is no learning step. Calibration is the 2T known-n samples on G. Check the identity on extra fresh terms, and close with the final kG = Q test.
- **Prior-art distinction.** Lange–Winterhof study polynomials in x(nG) that give n. Hess–Shparlinski and Beelen–Doumen bound the linear complexity of x(nG) over F_p. Fact A explains why those F_p results are strong. The F_q-valued, mixed-modulus, geometric-sampling version that tests every sparse exponent set at once is something I have not seen. The H014 and H016 screens were statistical correlations for one character at a time. This test is exact and closed under linear combinations.
- **Variant.** Running the same probe on F_p-valued features detects exact MCL structure, meaning combinations of multiplicative characters of order d with d dividing gcd(q−1, p^e − 1) for small e. It covers all such characters in one run.
- **Assumption (unsupported).** That some cheap coordinate map is secretly sparse in the log. I have no positive reason to expect this. The case for testing is that the class can be closed cheaply and exactly.
- **Cheapest decisive falsifier.** Run 4 features on 3 synthetic curves (q around 2^14, 2^17, 2^20) with T = 128.
  - My unmeasured estimate is about 1M events in total: roughly 257 scalar multiplications per curve plus 12 BM runs of length 256.
  - The outcome is exact. A random sequence reaches complexity about T, and complexity at or below T − s happens with probability about q^(−2s), so there is no multiple-testing correction.
  - Controls: a planted f* = P(log), built from a full offline table that is never given to the solver, must return its t. A random F_q table must return about T.
  - Optional second gate: test the span of monomials in X̄ and Ȳ of degree 3 or less with t ≤ 8, using block Hankel elimination (about 2.5e5 operations per curve).
  - Reject if every feature reaches complexity T.

## Card 2: low-agreement polynomials in the log, recovered by Reed–Solomon list decoding

This uses the same structure family as Card 1, but a different regime, decoder and test.

- **Mechanism.** Suppose f(nG) mod q agrees with some P(n) of degree L on a fraction ρ of n.
  - Calibrate on (n_i, f(n_iG)) with known n_i, and run Guruswami–Sudan list decoding to get P. This needs N > L/ρ^2 samples.
  - On the target side, collect (r_i, f(Q + r_iG)). Each sample costs one addition from a running table, and k + r_i is uniform, so the agreement rate is the same.
  - The decoded list contains P_k(r) = P(k + r).
- **Recovery.** Compare coefficients: coef_(L−1)(P_k) = c_(L−1) + L·c_L·k. So k = (coef_(L−1)(P_k) − c_(L−1)) / (L·c_L). Check each list candidate with kG = Q.
- **Work and memory.** About 2N additions plus two list decodings, so poly(L/ρ^2) in total. Memory is O(N). With fast decoders this beats sqrt(q) roughly when L/ρ^2 ≪ q^(1/2). With cubic Guruswami–Sudan, the condition tightens to L/ρ^2 ≪ q^(1/6).
- **Distinction.**
  - Akavia–Goldwasser–Safra and H003 use the heavy Fourier coefficients of a predicate.
  - Coppersmith–Shparlinski bound polynomial approximations of the log in the other direction, from element to log.
  - Here the feature is a noisy low-degree polynomial in the log, and recovery uses the shift-coefficient identity above. L = 1 is just a noisy discrete-log oracle and serves as a pipeline control.
- **Assumption.** That agreement is non-negligible at fixed small L. There is no supporting mechanism.
- **Falsifier.** Use the Card 1 features, L ∈ {1, 2}, and a RANSAC-style search: sample random pairs or triples to propose a candidate polynomial, then check agreement on 64 fresh samples with early abort.
  - At q = 2^20, a useful agreement ρ ≥ 0.03 needs about 1e4 pairs (L = 1) or about 4e4 triples (L = 2). That fits the cap.
  - A planted noisy-polynomial control must be detected.
  - Reject if the best agreement is at chance level.

## Card 3: approximate K-orbit invariants, with storage-based collisions and baby-step giant-step inside K

- **Mechanism.** Pick a subgroup K of F_q^* of order h, with h dividing q−1. Use a cheap label I: E → {0,1}^b that tends to stay the same along K-orbits.
  - Do not use a walk. Sample R = A_i + B_j from two labelled tables (one addition per sample), store I(R) with its labels, and wait for an I-collision.
  - A collision with R_j = [u]R_i for some u ∈ K gives a_j + b_j·k = u·(a_i + b_i·k).
  - Find u with baby-step giant-step (BSGS) inside K: about 2·sqrt(h) scalar multiplications, costing O(sqrt(h)·log q) additions. Then solve for k and verify.
- **Speedup formula (exact under independent sampling).** Let c = Pr[I(P) = I([u]P)] over random P and u ∈ K. A pair of samples gives a true collision with probability c·h/q.
  - Samples needed: N ≈ sqrt(2q/(h·c)), and memory is the same.
  - Total work ≈ N·(C_add + C_I) + (1 + n_sp)·O(sqrt(h)·log q), where n_sp ≈ N^2·kappa_I/2 counts false collisions between different orbits.
  - Any gain needs h·c > (1 + C_I/C_add)^2, plus kappa_I ≪ c·h/q.
  - Sanity check: K = {±1} with x as the label gives the known sqrt(2), and j = 0 automorphisms give sqrt(6).
  - With h ≈ q^(1/2) and a polylog-cost I, the total is about q^(1/4).
- **Two exact limits.**
  - *Subgroup necessity.* An exact or high-consistency K-invariant is also invariant under every μ_ℓ inside K. So testing small ℓ is a necessary test for all larger K that contain μ_ℓ.
  - *Small-integer degree bound.* If K contains an integer u with |u| ≥ 2, any exact invariant rational function of degree d satisfies d ≥ q/(u^2 + 3). Proof: g∘[u] − g has degree at most d(u^2 + 1) and vanishes on at least q − 2d points. It cannot be identically zero, because the degrees d·u^2 and d differ. For generic K this bound is vacuous, so it does not settle the question.
- **Distinction.** The repo already has the exact-invariant bridge and BSGS inside K (H003 shared recovery) and enumeration canonicalization (H013 card 3). The older work in this area is Duursma–Gaudry–Morain, Wiener–Zuccherato and Gallant–Lambert–Vanstone. What is new here:
  - the tolerance formula sqrt(h·c);
  - the sampler that costs one addition per sample instead of one scalar multiplication per transition;
  - the q^(1/4) balance point;
  - the necessity argument and the degree bound;
  - label-free training on (P, [u]P) pairs, which need no discrete logs.
- **Training and generalization.** Each training pair costs one scalar multiplication. Per-curve training is single-target work and must stay ≪ N. Validate on held-out points, and on fresh curves for any uniform model.
- **Assumption.** That a polylog-cost I with c ≫ kappa_I exists on generic curves. I have no mechanism for it. The maps [u] have degree around q^2.
- **Falsifier.**
  - *Stage A (exact, very cheap).* Use generic curves with q ≈ 2^16 to 2^20 and q ≡ 1 mod 3, and K = μ_3. Take V = span{x^i·y^j : i ≤ D, j ≤ 1} with D up to 50. Find the kernel of g ↦ g∘[λ] − g on 2·dim(V) points, then confirm on fresh points. This costs about 5k group operations plus a ~3.5e5 elimination.
  - *Planted control.* A j = 0 curve must return x^3 in the kernel.
  - A kernel of constants only rules out low-degree exact invariants for every K that contains μ_3.
  - *Stage B (only if A fails, as I expect).* Train a capped contrastive learner, and require the j = 0 control to reach c ≈ 1. Park the card if held-out c ≤ 2·kappa_I at all three sizes.

## Routes I checked and did not card

- **Point counts as features** (for example, the trace of v^2 = (x − x(Q))·f(x)). They are polylog features of Q, but they average over translations and never involve [k]. Bringing in the graph of [k] is the marked-surface card (H002 V1).
- **Searching the isogeny class for a weaker model.** p, q and the embedding degree are fixed across the class, so only arithmetic constants change.
- **Class-group cycle endomorphisms.** They are polylog to evaluate and have a known eigenvalue, but that eigenvalue has large order. A 2D decomposition still lands at Gaudry–Schost sqrt(q), and canonicalizing an orbit needs enumeration.
- **Pollard–Strassen-style polynomial BSGS.** The giant-step parameter enters through the group, not polynomially, so there is no speedup.
- **Group subset sum with representation techniques.** It needs an approximate homomorphism to a small group, which amounts to scalar leakage (consistent with the repo's Freiman note).
- **Canonical q-torsion lift to Z/p^2.** It is an exact homomorphism, but the resulting discrete-log problem is isomorphic, and its coordinates are just another feature (H003).
- **Compressed sensing of the log.** It reduces to H003 or to Card 1.
- **Shared inversion for P ± M steps, and skipping y in composite steps.** The first is known (the Wang–Zhang line). The second breaks negation canonicalization.

## Suggested order

1. Card 1 Berlekamp–Massey test (exact, about 1M events).
2. Card 3 Stage A kernel test with the j = 0 control (tiny).
3. Card 2 RANSAC test.
4. Card 3 Stage B, only if Stage A is unexpectedly positive.

Any root run should freeze the protocol and charge all costs, as in H014.
