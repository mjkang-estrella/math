# SUMMARY — lane pi-han-pedon-higher-shifts-r1

**Target.** Full substantive resolution (proof or refutation) of Conjecture C of
Han–Pedon (arXiv:2610.36132v1, 26 Oct 2026): for every n >= 1 and ell >= n+3, every
residue subsequence Delta_{r+m*rho_n}^(ell)(Phi_n) (rho_n = 2n(n+1) for even n,
4n(n+1) for odd n) equals an integer-valued polynomial Q_{ell,r}(m); together with the
still-open old E(2) unboundedness for every ell >= n+3 (printed-index typo not counted).

**Outcome. NO full resolution.** No proof of Conjecture C and no refutation. Honest
no-result on the nominated object, with substantial verified partial progress. Credit 0;
nothing nominated; no Lean endpoint (no complete theorem to formalize).

**What was delivered.**

1. PROVED (short, rigorous, written out in FINDINGS.md Section 1): the universal Hankel
   T-system Delta_{k+1}^(s) Delta_{k-1}^(s+2) = Delta_k^(s) Delta_k^(s+2) - (Delta_k^(s+1))^2
   (classical Desnanot–Jacobi ingredient; applied here as a reduction, not claimed new),
   plus its exact consequence Proposition 2: with the source-proved periodic data for
   shifts s <= n+2, the shift n+3 sequence obeys an explicit first-order recursion with
   periodic coefficients, giving affine residue quasi-polynomials away from an explicit
   finite set of "double-zero" indices — gap (d) documented precisely.

2. COMPUTED and CROSS-VALIDATED (exact integer arithmetic, two independent methods):
   full Delta^(ell) sequences for (n,ell) = (1,4..8), (2,5..7), (3,6..7) up to j ~ 440,
   every value checked against direct Bareiss determinants; reproduction of the source's
   own printed ell=n+2 period as implementation validation. Data: notes/conjectureC-data.json.

3. VERIFICATION RESULT: Conjecture C holds with exact quasi-polynomial fits on every
   residue class of all ten tested (n,ell) pairs (27-53 points per class for n=1; 25-31
   for n=2; 9-10 for n=3). No refutation found. Unboundedness (E(2)) confirmed on the
   same data. Explicit factorized quasi-polynomials recovered for n=1, ell=4..7.

4. STRUCTURAL DISCOVERIES (computational, exact):
   - the higher-shift H-fraction orbits are NOT eventually periodic; they drift forever
     (eternal passes; for n=1, ell>=5: sigma_j = 0 identically, so Delta_j^(ell) != 0
     for all j; degrees of the A_m triples fixed at (ell-1, ell, ell+1));
   - the quasi-polynomiality mechanism: partial products w_j = prod v_i tend to +-1 with
     1/j deviation; Delta_j = prod_{l<j} w_l telescopes through Pochhammer-type ratios
     into exact polynomials;
   - minimal degrees for n=1 follow the Fibonacci law 1,2,3,5,8 (= F_{ell-2}) for
     ell = 4..8 (empirical).

**Smallest remaining gap** (FINDINGS.md Section 2(d) and 5): (i) the double-zero classes
not determined by the T-system recursions; (ii) a uniform parametrization of the drifting
NextABC orbit families across all ell >= n+3 (the ell=4,5,6,... families differ; slope-20
factors appear at ell=7). Both are precise, finite-looking obstacles; neither was closed.

**Strongest objection/falsifier**: all positive evidence is exact but finite (j <= 440);
a residue class deviating from polynomiality beyond that range cannot be excluded by this
lane's data. Conversely, Proposition 2 must not be read as a proof of the conjecture.

**Provenance**: provenance.json (URLs, SHA-256, access dates, search response ids,
access limits: ScienceDirect 403 for Wang–Xin–Zhai body; everything else read directly).

**Scope**: only this lane written; no git/staging; no external messages or uploads;
no polling of the unrelated asynchronous reviewers (Kilbas, beta-prime); jobs bounded
(<512MiB, j <= 440, series precision <= 12000).
