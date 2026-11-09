# Structural discovery r91 — 29 October 2026

Disposition: UNRESOLVED, ZERO CREDIT, NO NOMINATION. Counts remain 8 additional / 38 total. No complete ordinary source resolution, PROOF.md, formal development, or paper. Solo research; no children, git operations, shared/other-lane edits, browser, account/contact/post/upload actions. The initial report inventory briefly used /tmp/r91-search-tmp and was moved into this lane; this was a scope mistake, not a shared research edit. All subsequent artifacts are here.

## Context and overlap

Read ancestor and batch AGENTS, current NEXT, ledger and prior-campaign-context. Full JSON and NEXT contents with hashes are retained in context.json. Read root-edge-irregulator-final-freeze-r1/ADOPTION.json and r88 discovery/current-registry account. Inherited baseline: 350197 Omega and 174524 OpenAI inventory entries; preserve incomplete semantic coverage and the chronology of the r85/r88 deltas. Do not treat catalogue counts or status badges as theorem evidence.

Before source investment, the all-date `rg -l` report search included FINDINGS, discovery, SUMMARY and provenance filenames across the entire research tree; report-inventory.txt records it. Exact later search also included REPORT/COMPARISON and found r61's Mühlherr–Poullot acyclic-orientation work. Read that actual discovery report: its grid chromatic-count refutation is unrelated to coherent paths on hypersimplices. The author overlap does not establish mathematical overlap or freshness. Available r89 notes and its arithmetic fiber code concern finite/arithmetic work; r90 fetch inventory concerns gamma/median/special-function analysis. No claim to know unpublished parallel progress. Honored all named exclusions, including r88 six-matrix Fuss–Narayana, Toeplitz+Hankel and distance-signless spread.

## Three precise primary screens

1. Yan–Mao–Wang, arXiv2309.01123v1, Conjecture 1 (p2). For every finite graph G, real tau, and integer m>=2, let A_tau=A+tau D and W_tau=[e,A_tau e,...,A_tau^(n-1)e]. The proposed absolute determinant identity for G rooted-product with an endpoint-rooted P_m has factors det(A_tau(G))^floor(m/2), det((1-tau²)I+tau A_tau(G))^floor((m-1)/2), and det(W_tau(G))^m. Read actual Conjecture1, Proposition3 and its proof reducing the claim to a Chebyshev-type resultant, and the source's theorem-proof endpoint. Also read 2601.01542v1 Theorem3 and its complete pp7–8 proof: an arbitrary-rooted-graph resultant factor times det h(M(G)) times det W_M(G)^m, derived from eigenvector tensor products and Vandermonde/resultant products. This is a close general theorem, but h still requires evaluation and its displayed formula is not automatically the exact conjecture. Deferred: high source-adaptation/subsumption risk, no assertion of an already public exact resolution, no computational or proof investment in a new claim. The mistakenly requested nonexistent v2 returned404; the official arXiv record identifies v1 only. Subsequently reading the real v1 is version correction, not access-control evasion. Journal VoR not compared.

2. Grosdos et al., *Exact solutions in log-concave maximum likelihood estimation*, AAM143(2023)102448, DOI10.1016/j.aam.2022.102448, Conjecture3.4 p14. For a point configuration in R^d with maximal regular triangulation Delta, the highest total-degree part of the numerator of its score-matrix determinant is proposed to be product_j sum_(sigma containing j) vol(sigma) product_(alpha in N(j) outside sigma)(y_j-y_alpha). Read the full actual Theorem3.1 proof pp12–14, not merely the indexed conjecture. It already clears each column by squared edge differences and proves diagonal degree dominance. Passing to a once-per-column denominator and studying cancellation looks like a routine extension of that exact proof; the word 'numerator' also requires an exact reduced-denominator comparison. Screened out for this assignment before trying to count an adaptation or normalization correction. No resolution of the conjecture is claimed.

3. Selected: Germain Poullot, *Vertices of the monotone path polytopes of hypersimplicies*, arXiv2411.14102v3, Proposition5.4, Conjecture6.2 pp20,23. Initial v1 November21,2024; current v3 October23,2025, confirmed from official live arXiv history. The same concrete recurrence appears in Germain Poullot's Problem6, Oberwolfach Report58/2023, pp3308–3309. Read actual Proposition5.4 proof, Theorem5.6 full induction and Theorem5.7 proof/eigenvalue expansion. The latter already supplies eigenvalues and positive binomial expansions; these are not new results here. Later Juhnke–Poullot arXiv2504.20739v1 April29,2025 and CURRENT v3 August11,2026, Example3.8/Problem3.9 retain this exact target as a question. Read the actual current Example3.8 and neighboring Theorem3.11 derivation: prism counts are ell*N_(ell-1), a different transformation. Their general-polytope counterexamples do not refute the hypersimplex conjecture. The thesis URL returned500 once, with no retry or workaround; its body is not admitted.

## Exact full target

For integers n>=4 define the three polynomials by

    T4=z^4+2z^3, Q4=z^4, C4=2z^4+2z^3,
    T_(n+1)=z T_n+(1+z)(Q_n+C_n),
    Q_(n+1)=(1+z)Q_n+z C_n,
    C_(n+1)=(z+z²)T_n+(1+z)C_n.

Set V_n=T_n+Q_n+C_n=sum_k v_(n,k) z^k, with coefficients outside the support zero. The primary Conjecture6.2 asks v_(n,k)^2 >= v_(n,k-1)v_(n,k+1) for EVERY n>=4 and every internal support index 3<k<floor(3(n-1)/2). This is the full coherent-path length distribution, not a partial n range. The report additionally asks ultra-log-concavity; we use the precise ordinary conjecture as the primary minimum target. For degree d, the stronger full-polynomial normalization requires k(d-k)v_k² >= (k+1)(d-k+1)v_(k-1)v_(k+1). No discovery is claimed from the report's indexing slips.

## Sustained uniform proof work

Write a=1+z. The exact invariant C_n=a(T_n-Q_n) holds initially and is preserved: if D=T-Q, then D'=zT+C=zQ+(1+2z)D, while Q'=a(Q+zD), and C'=aD'. Thus the three-state recurrence reduces, for all n, to the POSITIVE two-state update

    Q'=aQ+azD, D'=zQ+(1+2z)D,
    Q4=z^4, D4=2z^3, V=2Q+(2+z)D.

Its trace is 2+3z and determinant 1+3z+z²-z³. Cayley–Hamilton yields the exact scalar recurrence

    V_(n+2)=(2+3z)V_(n+1)+(z³-z²-3z-1)V_n   (n>=4).

The negative coefficients of the second multiplier prevent a direct positive-coefficient log-concavity induction. The already-source eigenvalues are (2+3z +/- z sqrt(4z+5))/2, not a new mechanism.

A second route removes that signed multiplier via a shifted Fibonacci expansion. For r=n-4, introduce H0=4a, H1=a²+6a+1 and H_j=H_(j-1)+aH_(j-2). Exact formal power-series algebra gives

    sum_(r>=0) V_(r+4)t^r
      = z³[4a+(z³-4a)t]/[1-(2+3z)t+(1+3z+z²-z³)t²]
      = z³/(1-at) * [4a+(z+2)²u]/[1-u-au²], u=zt/(1-at).

Taking coefficients using [t^r]t^j/(1-at)^(j+1)=binom(r,j)a^(r-j),

    V_(r+4)=z³ sum_(j=0)^r binom(r,j) a^(r-j) z^j H_j.

This positive formula retains all n but proves neither log-concavity nor ultra-log-concavity: arbitrary sums of log-concave summands need not be log-concave. It is a diagnostic reorganization of source eigenvalue algebra, no nomination.

A third route seeks a preserved synchronization cone. Set E=zD. Then

    (Q',E')=(a(Q+E), z²Q+(1+2z)E), (Q4,E4)=(z^4,2z^4).

For nonnegative sequences p,e, synchronization means both are log-concave and p_k e_k >= max(p_(k-1)e_(k+1),p_(k+1)e_(k-1)). Actual orbit pairs pass through n100, but this cone is NOT preserved in general. Exact synchronized inputs p=(1,1,1), e=(1,4,1) map to Q'=(2,7,7,2), E'=(1,6,10,3,1). E' fails log-concavity at k3:9<10. Hence neither the usual synchronization hypothesis nor generic componentwise log-concavity closes induction. Independently, original three-state inputs T=(1,1,1), Q=(4,2,1), C=(1) are all log-concave, while the resulting sum (10,17,9,5,1) fails at k2:81<85. These are METHOD counterexamples, not allowed initial data and not source refutations.

## Checks, gap, objections, falsifiers

check.py verifies 745500 ULC inequalities, including trivial zero/boundary entries, for all four source polynomials n4..500; 496 exact scalar-recurrence comparisons; and21 positive-formula identities r0..20. invariant.py verifies the source invariant and pair synchronization through100 and the explicit generic cone obstruction. reduction.py independently obtains the characteristic polynomial and rational generating function using exact symbolic arithmetic. All pass under the copied guard. This extends finite evidence, not proof or credit.

Exact mathematical gap: a uniform inequality for every n and every coefficient index of this one fixed orbit. A stronger preserved cone, a coupling/injection for the positive finite sum, or an all-order coefficient inequality is still missing. The source's spectral/degree formulas and our reduction do not fill it. Strongest mathematical objection: even synchronized LC pairs fail under the positive reduced update. Strongest eligibility objection: the public registries are only boundedly screened; neither alias-free semantic coverage nor worldwide priority is established. No independent eligibility review was performed.

Falsifier for ordinary source claim: one allowed n,k with exact v_k²<v_(k-1)v_(k+1). Falsifier for the stronger report claim is an exact failure of the displayed ULC inequality; that alone would not refute ordinary Conjecture6.2. Falsifier for any proposed future invariant is an allowed source orbit escaping it or a valid cone input whose image fails, as above. A public full proof with a source-to-source bridge would defeat a freshness claim; none is asserted here.

## Current registry and proof-body boundaries

Fresh HTTP at18:53:53Z observes Omega549177fd878744e25dce688cbf94dc2955e8958f and OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Comparison from r88 e9c949019b00eb22ab88e81d6ac6b1047925d95d returns14/14 commits and10 files. Saved patches/path screen has no exact topic hit; omitted patches and semantic aliases remain limits. Retain r88's earlier13-commit/194-file delta from6f8ee6614e0faf9dfa2cce46d1eb758dea97c335; do not retroactively replace its dated evidence. No full recursive current tree or all-body content audit was performed.

Read current pinned Omega crown-order-polytope problem, then its Blueprint and actual formal theorem body saved as crown-proof-body.txt. The Blueprint 'machine-checked' sentence alone was insufficient. Actual body constructs even/odd Chebyshev factorizations of an auxiliary polynomial, real splitting, Newton coefficient bounds, and three low-degree corrections for GEOMETRIC CROWN FACE COUNTS. It does not state a generic transfer-matrix LC theorem or our length distribution. No corresponding real-rooted auxiliary factorization/transport has been proved for V_n. Reading this body does not verify every dependency or establish a whole-repository non-subsumption verdict. No imported Lean file was built or used as a new certificate.

http.json records exact URLs, UTCs, status, byte counts, hashes and errors. No403/429/challenge was encountered in this lane. Resource caps: AS and sampled process-group RSS512MiB, CPU210s, wall230s, nominal40ms sampling, BLAS1, copied improved packet helper_guard.py; no cap raises. Finalizer logs are deliberately excluded from hashes. run.sh replays local exact checks without network. Honest zero; no count changes.
