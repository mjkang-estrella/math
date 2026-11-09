# discovery.md — pi-han-pedon-higher-shifts-r1 (2026-10-28)

Worker: Pi GLM-5.3-Flash-EXL3, thinking=high, standard speed. Solo; no children.

## What was searched for and read (chronological)

1. Read ancestor openai-proof-research/AGENTS.md, batch AGENTS.md, ledger.json,
   prior-campaign-context.json, NEXT.md, and the prior-campaign metallic-Hankel
   artifacts (2026-10-26 euler-turan lane's Lean proof of old E(1) at shift n+2 —
   excluded from rediscovery).
2. Downloaded and read the actual primary sources:
   - 2610.36132v1 (26 Oct 2026): Theorem A (eventual periodicity of H-fraction of
     Phi_n^{(n+2)}, period p_n), Theorem B (ell=n+2 case of E(1): 2n(n+1)-(anti)
     periodic, values -2..2), Conjecture C (the open object), Algorithm NextABC,
     Lemma 2.6, Prop 2.7, Theorem 2.2 (Han16), Remark 4.5, appendices A-H structure.
   - 2502.05993v2 (17 Jan 2026): Conjecture E (old), Theorem F (mod-p periodicity for
     all shifts), Lemma 7.1/Prop 7.2/Theorem 7.3 (shift tails), Example 7.4.
   - GitHub GuoniuHan/metallicplus (read-only clone): nextabc.sage, README; the repo
     contains NO higher-shift data — Conjecture C came from unpublished concrete-n
     experimentation by the authors.
3. Bounded prior-art searches (response ids in provenance.json): no resolution or
   follow-up of Conjecture C exists; closest technique prior art is Wang–Xin–Zhai
   1806.08927 (Adv. Appl. Math. 2019), "Hankel determinants and shifted periodic
   continued fractions" — body inaccessible (HTTP 403), abstracts only; it does not
   treat metallic higher shifts, whose H-fractions are NOT shifted-periodic (our
   Discovery 1).

## Discoveries (epistemic status in parentheses)

D1. The universal Hankel T-system (PROVED; classical ingredient — Desnanot–Jacobi —
    applied as a reduction): Delta_{k+1}^(s) Delta_{k-1}^(s+2) =
    Delta_k^(s) Delta_k^(s+2) - (Delta_k^(s+1))^2. Verified exactly on 48 instances
    for n=1 (checks/check_tsystem.py).
D2. Reduction (PROVED as far as stated): with source-proved periodic data for
    s <= n+2, the shift-(n+3) determinants satisfy an explicit affine recursion with
    periodic coefficients and periodic forcing on all but finitely many residue
    classes per period; the leftover "double-zero" classes are precisely identified
    and are a genuine gap (for n=1: k ≡ 1 mod 4, values 4m+2).
D3. Higher-shift H-fraction orbits drift forever (COMPUTATIONAL, exact): not
    eventually periodic for ell >= n+3; a_m are rational functions of the block index
    (n=1, ell=4: a_{3j+4} = -((2j+3)^2-1)/(2j+3)^2, ...); for n=1, ell >= 5,
    sigma_j = 0 identically and Delta_j^(ell) != 0 for all j.
D4. Partial-product mechanism (COMPUTATIONAL + partially proved): Delta_j =
    prod_{l<j} w_l with w_j = prod_{i<=j} v_i; the w's are explicit quasi-rational
    functions (n=1, ell=5 fully computed), and integer-shift Pochhammer telescoping
    produces the exact integer-valued quasi-polynomials.
D5. Verification of Conjecture C on 10 (n,ell) pairs to j <= 440 (COMPUTATIONAL,
    exact, cross-validated): all residue classes fit exact integer-valued
    quasi-polynomials; explicit factorizations recovered (n=1, ell=4..7); degree law
    for n=1 is Fibonacci (min degrees 1,2,3,5,8 = F_{ell-2}); E(2) unboundedness
    confirmed on the same data. No refutation found.

## What was NOT achieved

- No proof of Conjecture C for all parameters (the two obstacles: uniform orbit-family
  parametrization across ell; the double-zero classes). 
- No refutation (data supports the conjecture everywhere tested).
- No Lean endpoint (no complete theorem).
