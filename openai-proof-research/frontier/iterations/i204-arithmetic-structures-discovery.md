# I204: bounded arithmetic-structure discovery

2026-10-12. **NO VIABLE TARGET IN THIS ROUND.** No substantial nomination is submitted. Eight accepted findings remain eight; the two independent acceptance gates remain with the parent.

Work was confined to families 025, 027 and 028 and the assigned I204 files. All theorems and lower proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` were accepted. The work below studies proposed extensions, not upstream truth. No child agent, research code, numerical scan, test suite, snapshot collection, seal, historical replay, staging, commit or publication was used. Live Foulkes/elliptic follow-up outputs were not used as dependencies or edited; I31 and other tasks were not edited.

## Screening and reading

Read `AGENTS.md`, `sources/upstream.json`, the three catalogue entries and the complete path listing for these families. A bounded search of actual earlier reports and decoded dispatch strings was performed before deep proof work; the final expanded operation search covered 503 actual iteration Markdown/JSON files with iteration number below 198. JSON string fields, including nested serialized objects, were decoded. It found no earlier substantive target in these families. Matches were unrelated uses of “integral representation”, the I75 Gaussian factorization/Selmer problem, or the I196/I197 note correcting family 026 versus 027. This establishes the scope of this search, not an assertion that the topics have never been screened. Frozen copies were not counted as studies or searched recursively.

All 34 text/build files in the three supplied manuscript directories were retrieved through immutable raw URLs and read, including the nested Egyptian-fraction random-products file, both character-variety figure sources, references, and the full Gaussian coverage/schedule/information argument. The source manifest records individual URLs, hashes and scope. There is one manuscript per supplied directory and no separate companion manuscript there. The PDFs duplicating these build sources were not retrieved. The retained external Tenenbaum–Yokota paper was read through all seven pages of extracted text; uncertain OCR in some historical/displayed formulas is explicitly excluded from proof reliance.

The [analytic record](../experiments/i204_arithmetic_structures/analytic-attempt.md) contains the exact statements and proofs of the partials, including the two developed routes. [Reading limits](../experiments/i204_arithmetic_structures/reading-and-failures.md), [input authentication](../experiments/i204_arithmetic_structures/input-authentication.json), and [primary literature notes](../sources/i204_arithmetic_structures/literature.md) are separate.

## 025: selected target and two routes

The selected target was a genuinely stronger *simultaneous* assertion: absolute constants A,C,b0 such that every integer b>=b0 and every 1<=a<b admits a distinct expansion with at most `C loglog b` terms and every denominator at most `b^A`. It is **unresolved here**. The bounded literature search did not certify its worldwide open status.

The source's `thm:main` minimizes length with unrestricted denominators. Its `prop:density`, `lem:residues`, and descent provide the actual common auxiliary denominator and recursive identities. Its entire `prescribed.tex` was also read: exact markers, marker-preserving padding, rational-divisor supply, and the explicit prescribed-length estimate are already paid operations. They are not new candidates.

**Route A: control the source recursion's denominator cost.** The hoped-for estimate was that the product of rescaling integers z along a short path stays polynomial in b. A backward predecessor count shows why a direct implementation cannot do this for its dense family. In the notation of the analytic record, with `X=exp(H S)`, `M<=exp(A S)`, `C>=exp(L S)` and `L>H>1`, even allowing every divisor of M, all but `X exp(-gamma S)` starting numerators need more than `theta log S` high-stage reductions before reaching numerator at most `exp(S)`. Each such step has `z>=exp((L-H)S)`. Thus the literal recursive sum emits a denominator at least `exp(c S log S)`. All constants depend only on the fixed source size constants, uniformly over M and C. The proof uses elementary divisor counting and covers early zero remainders and level jumps.

This is a proved **method limitation**, not a lower bound on optimal Egyptian expansions. Subsequent algebraic replacements can change the emitted denominators. The remaining gap is a new representation/cleanup mechanism with a polynomial size budget, or a different dense-family construction. No such mechanism was obtained.

**Route B: use sparse divisor sums of one polynomial-sized common denominator.** A sufficient condition is `Q=bM<=b^A` and an expansion of each aM as `O(loglog b)` distinct divisors of Q. Two exact obstructions were proved:

* For odd prime p, allowing all `Q=p 2^t<=p^A`, at most `p^{o(1)}` of the p-1 possible numerators can be represented with `C loglog p` divisors. This follows by counting subsets of the `O(log p)` divisors, even when t depends on the numerator.
* For every fixed epsilon in (0,1), all sufficiently large primes p, and all `M<=p^{1-epsilon}`, `(p-1)/p` has no distinct expansion whose denominators all divide pM, without any term-count restriction. The positive integer `S0+M`, with S0 a sum of distinct divisors of M, would be divisible by p but smaller than p.

The second statement concerns a *common denominator*, not the largest denominator. This distinction is essential: their least common multiple may be much larger than each term denominator. Divisor-rich reservoirs escape the binary counting obstruction, but the needed short, positive, exact subset sums were not constructed. The known divisor grouping and the source's rational-divisor supply do not supply them for a single Q of polynomial size.

Two additional technical checks prevent false nominations. First, any k-term positive expansion of a/b has `n_j<=(kb)^{2^{j-1}}` after sorting. Combining this with the accepted length theorem only gives a stretched-logarithmic cap `exp((log b)^E)` for some absolute E, not a polynomial cap. Second, when `(p-1)/p` has largest denominator N<p^2, setting `M=floor(N/p)` gives `p<=(k+1)M^k` by reduction modulo p of the p-divisible denominators. Thus `N<=p(log p)^a` cannot coexist with double-logarithmic length. This elementary obstruction is not new literature: the primary [Tenenbaum–Yokota paper](https://tenenb.perso.math.cnrs.fr/PPP/Egyptian.pdf), p.151, reports a stronger simultaneous lower obstruction due to Yokota. Its near-linear-cap upper theorem also uses order `log b/loglog b` length.

## 027: no new arithmetic constraint proved

Read `thm:main`, all free-module flag operations, `thm:diagram-density`, both closed-surface steps, and the determinant/quotient descent. The source already gives one field independent of components and exact complex Jordan classes. Its `lem:uniform-field` is not a new extension construction.

The elementary principal-congruence subgroup argument gives density with any fixed congruence condition for free-group representation tuples. It is only a technical extension of the source's free-group case. It does not pass a surface relation or prescribed peripheral classes.

A stronger all-finite-prime Jordan condition cannot be deduced from selecting a complex open stratum: `[[1,2],[0,1]]` is nontrivial unipotent over C and becomes the identity modulo 2. The required minors must generate the unit ideal, a condition the source's open-locus selection does not enforce. This counterexample refutes the proposed inference, not a general existence theorem for other points. No congruence-compatible rank reduction or strict-boundary density mechanism was proved.

Primary [Coccia–Litt](https://arxiv.org/html/2507.00167v1), Theorems 1.1.2 and 5.0.2–5.0.4 and Remark 5.0.5, already supply rank-two potential density and an integral dense mapping-class orbit. Only the stated passages and their surrounding proof/context were read here; this is not a full independent review of that paper.

## 028: no new effective mechanism

The full source already proves a finite periodic obstruction (`thm:sieve`) and a modulus-dependent component bound (`prop:periodic`). Both shared-data coverage transfer and the final common-law telescope were read. Tracing their large-scale thresholds would be constant extraction, which the brief excludes.

A finite quotient graph with displacement-labeled edges gives a routine certificate: its lifted components are finite exactly when all fundamental cycle displacements vanish. Together with CRT this replaces Q squared in the source's bound by `V=product(p-1)^2`, and counts the exceptional primes as `8|P|`. This is a technical periodic-graph refinement, not a new prime-selection estimate. Enumerating and checking possible sieves is merely a search consequence of the accepted theorem; no search or code was run. The missing input is a new a priori D-dependent prime-selection/scale estimate beyond extracting the source's inequalities.

The primary Vardi PDF was located, but its extracted text at Proposition 6.2 was unreadable. No independent content claim rests on that extraction; the source's attribution to Vardi is not upgraded to a verified external proof. Current primary searches found no effective result to use for a new nomination within this screen.

## Outcome and limits

The completed work consists of proofs of technical consequences and obstructions, not only a plan or title survey. None meets the requested substantial-contribution gate. The most useful surviving question is the polynomial denominator cap, but both developed routes still lack the requisite construction. There is no conditional result offered to fill the quota, and no claim of a ninth finding. Detached output hashes are returned separately; the authentication record contains the retained source hashes without recursive provenance or self-hashing.
