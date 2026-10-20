# Arithmetic r100 handoff

PREFREEZE: no frozen target, no author proof, no nominee. No mathematical gate, contribution gate or count is assigned.

Runner: Factory Droid / claude-opus-5-5 / high. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Direction A: family 024, the k=3 least-preimage seed (unpaid)

The pinned companion's `thm:companion` gives, for each integer k≥1, an explicit asymptotic for the least-preimage count N_k(x) and a dichotomy: N_k(x) ≍ V(x) iff some totient d has ℓ(d) > kd. The source proves the positive arm for k=1,2 (Ford's d = 2^18·257) and explicitly leaves k≥3 undecided; the conjunction over all k is Erdős's open problem #51.

This round reduced the missing seed condition exactly (report A.2, elementary, checked): ℓ(d) > 3d iff the least preimage's radical S satisfies g(S) = ∏_{p∈S} p/(p-1) > 3; cheap radicals are classified in arity ≤ 3 (a triple is expensive iff it contains {2,3}) and the arity-4 boundary is shown to be delicate ({2,5,7,31} expensive, {2,5,7,37} cheap); necessary filters (d+1 composite, d not 2^A3^B, no two-prime preimages, …) are explicit. The divisibility route (all preimages divisible by 42 or 30 would suffice) passes through Ford's open k=6 question, verified verbatim in his Section 7.3: "It appears that there might not be any totient, all of whose pre-images are divisible by 6, but I cannot prove this" — and Ford notes non-existence would imply Carmichael's conjecture, so the negative arm is Carmichael-hard. SEED3 itself is strictly weaker than common divisibility (report Lemma A5), so both sides remain open. r3's exact barrier (log ℓ(d)/d ≤ σ(d)/d via the injection p ↦ p−1 into divisors of d) is restated; it does not exclude SEED3 at fixed support, and r3's 129-totient experiment found nothing past Ford's 257/128. No construction principle exists; a blind search is unmotivated. Bounded web searches (4 queries, recorded) found no known witness and confirm Erdős #51 open.

**Exact unpaid obligation:** exhibit one totient d with a certified complete inverse fiber and ℓ(d) > 3d (r3's exact-cover certificate format suffices), or prove none exists.

## Direction B: family 182, degree-only exponent at prime arguments (unpaid)

The pinned integer paper has a power-saving exponent c_k depending only on the degree; the pinned prime-arguments companion only c_h, C_h depending on all coefficients. The refinement DEG (prime-arguments bound with degree-only exponent; constants unrestricted) was already isolated by the i99 scout, which falsified the stronger height-free variant and declined a substantiality claim.

This round audited the prime paper's parameter chain (local → tuples → descent, files read): δ = 1/(100k·2^k) is degree-only, but the cycle length L must be divisible by p^{E_p} for every p below the h-dependent threshold P_1, the tuple dimension is d = (L!)^{2t+1}, and the induction needs M_0^{s_0}(1−3ρ*/4) < 1 with ρ* = M_0^{1-L}, M_0 = ∏_{p<P} p^{E_p}; hence the delivered exponent c_h = a_0/d ≤ M_0^{1-L}/(k·(L!)^{2t+1}·log M_0)(1+o(1)). An explicit checked family h^{(q)}(x) = q(x−1)² + q(x−1)³ + (x−1)⁴ (prime-intersective, degree 4, content 1, leading coefficient 1) degenerates: h_q ≡ 0 (mod q) as polynomials, forcing P_1 > q, L ≥ q, M_0 ≥ q, so the proof's exponent decays faster than q^{-(1-o(1))q} at fixed degree 4. The h-dependence is intrinsic to this proof, not bookkeeping.

**Exact unpaid obligation:** a repair of the auxiliary family (e.g. content renormalization h̄_l = h_l/cont(h_l)) requires the divisibility closure cont(h_l) | λ(D)·cont(h_{lD}) for all l, D, plus avoidance transport for renormalized values and treatment of nonzero-constant degeneration mod p; then re-verification of the tuple/lift/kernel/descent chain. Alternatively, determine how the integer paper achieves degree-uniformity (its body beyond the introduction was not read). Whether DEG is true is unknown; no lower-bound obstruction is known.

## Other work

Fourteen further families screened (008, 030, 029-companion, 021, 012, 020, 022, 023, 025, 026, 153, 160 at source level; 004, 007, 011, 001, 002, 006, 010, 014 at catalogue level) — outcomes in `packet/public/screens.md`. Anti-repetition history checks: r74–r99 arithmetic territory, r52/r53/t024w (024's moving-window chain), totient-recovery r2/r3, i99, r78/r85/r96 screens. No old frozen scope touched; active r135 and t088p133 roots not entered.

## Inventory

- 30 retained pinned source bodies (families 024, 182+prime companion, 008, and screening introductions for 029/021/012/022/025/023/030/026/020/153/160), every git blob SHA-1 verified against the complete pinned preprints tree (13223 entries, not truncated); 8 fetched-but-unread files removed with receipts before sealing.
- No third-party primary acquired this round (Ford was read from r2's retained extraction, copied unchanged into history with its retrieval record).
- 16 unchanged history copies: briefs, AGENTS.md, r99 disposition/adoption/publics, i99 scout, totient-recovery r2/r3 records, t024w proof review, r95 family-history counts.
- Read limits and the two-segment (compaction) provenance are in `packet/public/reading-limits.md`.

## Seal

`FINAL.json` binds this outside report, the manifest, the verifier, the controls script and the public report. Take its detached hash from the parent handoff. Run the read-only verifier and the copied controls as described in `packet/public/reproduction.md`. `integrity-results.json` is written outside the packet by the controls run and must be hashed separately. Author notes and scratch under `notes/` and `work/` are outside the packet and unsealed. These artifact checks are not mathematical gates.
