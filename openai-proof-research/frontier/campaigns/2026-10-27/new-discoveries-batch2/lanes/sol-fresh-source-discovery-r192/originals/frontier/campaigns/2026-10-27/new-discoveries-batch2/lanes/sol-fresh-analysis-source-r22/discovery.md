# Unresolved: shifted multiple-star-polylogarithm subordination

Credit 0. No complete source resolution, PROOF.md, Lean, acceptance nomination or count change.

## Source and exact full scope

Jiangtao Li, *The derived set of multiple star polylogarithms*, arXiv:2609.03653v1, submitted 3 September 2026, Conjecture 1.6 (introduction, after Remark 1.5). Actual complete TeX and HTML obtained and the definition, conjecture, moment representation, strict-MLR proof, quotient argument and boundary-separation proof read. The discovery service's location description “after Section 5, Proposition 5.8” does not match this actual source; source numbering controls. No journal version or journal equality is asserted.

For every pair of nonempty finite positive-integer indices k,l, order k≻l means l is a proper prefix of k, or the first unequal component of k is smaller. Put

H_k(z)=Li*_k(z)/z=1+Σ_{n≥1} A_k(n)z^n,

A_k(n)=(n+1)^(-k1) Σ_{n+1≥m2≥…≥mr≥1} m2^(-k2)…mr^(-kr).

The conjecture asks BOTH (i) H_l=H_k∘p for a holomorphic p:D→D with p(0)=0, and (ii) every Taylor coefficient c_n of that unique map is strictly positive, with Σc_n≤1. Indices beginning in 1 are allowed. Infinite indices and unshifted polylogarithms are different statements and are not substituted.

## Reconstructed deductions and universal gap

A_k(1)>0 directly from its finite sum. Thus the inverse-function theorem gives a unique local analytic p, without assuming the conjecture. Comparing coefficients gives

c_1=A_l(1)/A_k(1),
c_n=[A_l(n)−Σ_{j=2}^n A_k(j) Σ_{n1+…+nj=n;ni≥1} c_n1…c_nj]/A_k(1).

The same identity is the exact recurrence implemented in check.py. It does not prove a nonnegative right side: increasing A_k values enlarge the subtracted terms. Equivalently Lagrange reversion gives

c_n=Σ_{m=1}^n ([t^{m−1}](t/(H_k(t)−1))^m)/m · [z^n](H_l(z)−1)^m.

The inverse coefficients in the first factor have alternating contributions. No all-order cancellation/positive representation has been established. The finite checks do not justify analytic continuation, disk image inclusion, or the coefficient-sum bound.

The source's Theorem 1.1 establishes univalence; Proposition 4.4 proves strict density likelihood-ratio order using positive integral transforms; Proposition 4.7 gives strict boundary argument/modulus comparisons; Theorem 4.8 proves disjoint translated boundary curves away from z=1. I reconstructed the weighted-average derivative signs and the two-angle separation argument. A tempting route is to turn these curves into nested image boundaries via Jordan/argument-principle reasoning. It requires a careful treatment of the possibly infinite boundary value at 1 and a global image-inclusion argument. No such bridge is claimed proved here. Even disk subordination would leave strict coefficient positivity unresolved.

If one DID prove all c_n≥0 and disk subordination, then Σc_n≤1 follows by monotone convergence from p(r)<1 for 0<r<1. That final implication is routine and is not separately eligible.

## Exact obstruction to a general moment/MLR shortcut

Consider H_w(z)=Σ_i w_i/(1−t_i z), with

t=(1/100,1/2,1),
l=(1/10,89/100,1/100),
k=(1/12,89/108,5/54).

Both weight vectors are positive probability vectors. Their ratios k_i/l_i are 5/6,25/27,250/27, strictly increasing. The moment sequences are completely monotone. The corresponding first two nonconstant coefficients are

a=5459/10800, b=107503/360000 for H_k;
c=57/125, d=23251/100000 for H_l.

For the unique local inverse relation H_k(p)=H_l, coefficient comparison gives

[z²]p=(d−b(c/a)²)/a=−4234364835507/203352396973750<0.

Thus probability-kernel normalization, complete monotone moments and strict discrete likelihood-ratio order alone cannot force coefficient positivity. This is a proof-method falsifier, NOT a polylogarithm-source counterexample: these atomic measures are not identified with any Li index. It also does not test every extra source-specific quotient/starlikeness property. Replacing the source by a general moment theorem without those extra properties would be invalid.

## Early excluded lead: actual public same-object refutation

Javaheri2610.33653v1, Section1 Conjecture1.3, conjectures N(a,b)=N*(a,b), with a,b≥0,a+b≠1 and N* the maximal n with n=1 or (a+b−1)²≤8ab sin²(π/n). Actual complete source TeX read. This is a revised 2026 claim; the 2006 journal predecessor is not assumed identical (direct PDF URL404).

The current complete Omega tree located Problems/javaheri-2026-cyclic-arrangement-conjecture-refutation.md and its actual Lean proof body. Both were fetched at immutable head fb587b0e94c9169d5d1076c186dd766253eb5255 and read, not inferred from badges. At a=6,b=1, N*=3 because sin²(π/3)=3/4 and sin²(π/n)≤1/2 for n≥4. The strictly positive triple (6,5,5) has LHS−RHS=364. Hence dimension3 fails; descent (source Proposition4.1) or the finite-supremum contradiction in the public proof defeats N=N*. This exact arithmetic is independently reproduced. No Lean replay is claimed. Existing public proof observed at 09:06UTC, pinned commit dated08:58:13UTC, precedes this lane's selection. Original addition-commit chronology could not be fetched: GitHub API403, stopped. This is enough to reject rediscovery, not a claim of worldwide first-publication priority. No stronger parameter variant is salvaged.

## Classical/subsumption objection at full strength

The strongest objection is that any proposed subordination part may already be a routine argument-principle consequence of the SOURCE's boundary separation and univalence, or of classical universally starlike-function theory. Even a successful proof of part(i) alone would be a partial/routine result and cannot earn credit. The all-index, all-order strict composition-coefficient positivity must be resolved substantively before further proof engineering.

Closest actual companion read: Kamano2406.10604v1, introduction definitions, §2 integral representation and order theorem/proof. It assumes real parameters 1≥z1≥…≥zr>0, (k1,z1)≠(1,1), and proves value ordering of a shifted shuffle-type function. Setting all zi=z∈(0,1) identifies its l* with H_k(z), so it supplies REAL value ordering, not disk subordination or inverse-coefficient signs. Published version DOI10.1080/10652469.2026.2652429 (31March2026) returned403; stopped. Actual journal equivalence is HOLD. Lewis1983 and Bakan–Ruscheweyh–Salinas2015 universal convexity literature remain unread primary-body gaps; no clearance from abstracts. Inverse-function theorem, formal power-series composition/Lagrange inversion, Hausdorff moment representation and elementary coefficient comparison are classical dependencies, uncredited.

## Bounded prior screen and access limits

Before developing the retained target, current heads and complete trees were fetched or bases verified unchanged: Omega D5 12478 entries + Problems1541; OpenAI preprints13578; Count183; AIM3541. Every scoped tree reports truncated=false. These are Git tree API objects, not 1000-entry contents listings. OpenAI root is NOT claimed recursively complete outside preprints; Omega outside D5/Problems likewise not asserted. Exact heads, immutable tree IDs and verified-base hashes: coverage.json. Full target path-screen output: path-screen.json. No target-matching Li resolution was located; this is path evidence only, not full-text absence. Broad generic Polylogarithm library paths are not automatically same-object proofs. Clopen current homepage and targeted arrangement/polylogarithm query pages were fetched; no matching polylogarithm item was shown. No exhaustive1027-record traversal or status-based proof claim.

Campaign reconciliation: governing AGENTS, ledger5/30 and35/60, NEXT, prior accepted30 context, direct past lane summaries, and Fenner review read; past-lane-exclusions.json preserves all available direct lane summaries/hashes. Arcsinh, Gamma-level, shifted-Jacobi, cascade and mean35 are credited and untouched. Excluded/held analysis families in the assignment were not redeveloped. Fenner excluded by Jin's14October original AIM proof, as explicitly adopted by root. No count authority.

Searches were public read-only source discovery only. Relevant arXiv IDs/titles, subordination/coefficients, Kamano and classical polylog convexity searched; no matching full resolution found. Search is bounded and incomplete. No MathSciNet/zbMATH sweep, journal clearance, independent review, formal proof or worldwide novelty conclusion. Source-level complete result remains missing.

## Reproducible checks and stopping point

Run OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 43s python check.py in this lane. Hard512MiB address space,35CPU-seconds,40second alarm, BLAS1, deterministic exact Fraction arithmetic. It verifies741 ordered pairs from39 indices (depth1..3, each component1..3) through degree9, every composition equation, independent binary-tail formula for A_k(1), the generic negative coefficient, and the public364 witness. No random or numerical inference.

The next useful mechanism must exploit the literal index recursion to control ALL signed inverse coefficients, or produce an exact negative coefficient for a genuine pair. More grids alone are not a resolution. No PROOF.md because no full ordinary proof exists.
