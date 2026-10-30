# r141: full function-field LCM conjecture unresolved

Proposed discovery credit: **0**. The controlling totals supplied by the user are 9 additional / 39 total, next 40. No count, shared record, Lean file or manuscript is changed.

## Selection and early screening

The first search pool exposed published resolutions (Fibonacci sums; Fel syzygies) rather than eligible new work. No claim of independently resolving those problems is made. Merikoski–Haukkanen–Sasaki–Tossavainen's generalized LCM–GCD eigenvalue question is old: r87 discovery.md was reopened in full and its public half-resolution and missing converse read. It was dropped before downloading its source. The unrelated Yaqubi matches belong to Latin squares/Hetyei. A broad unanchored `Entin` search also matched words such as “sentinel”; these collisions are not scientific matches or freshness evidence. The corrected word-boundary author/title/ID/DOI query found no match in 1,701 retained/refreshed original-role report paths. The index reuses r138's qualified r137/r133-derived path/hash evidence, adds nine changed/new paths, has no hit cutoff, and retains original r111–r113 science. It is a named-role index, not a claim to have read every file in the project. Broad collision displays were clipped; no full semantic reading of those unrelated bodies is claimed.

The selected fresh source is Alexei Entin and Sean Landsberg, *The least common multiple of polynomial values over function fields*, Acta Arithmetica 217 (2025), 159–187, DOI 10.4064/aa231205-20-8, Conjecture 1.1 (journal p161; arXiv v4 p2). The actual current arXiv statement, journal statement, definitions, Proposition 4.1–4.2 proofs and the Theorem 1.8 special-polynomial proof were read. Source retrieval records give real UTC, URLs, access status and SHA256. ArXiv history currently lists v1 6 October 2023 and latest v4 4 January 2025; publisher gives online publication 7 January 2025. No journal scope is inferred only from its abstract.

## Exact full target

For **every** prime power q and **each fixed irreducible** f in F_q[T][X] with degree d>=2 in X, define M_n to consist of all monic degree-n polynomials in T. Let L_f(n) be the polynomial LCM of the values f(Q), Q in M_n. Define V_f={g in F_q[T]: f(X+g)=f(X)} and c_f=1/|V_f|. The question is whether

    deg_T L_f(n) / (c_f (d-1) n q^n) -> 1 as n -> infinity.

Both f and q are fixed in the limit. Absolute irreducibility and separability are **not** additional hypotheses. Polynomial units do not affect degree. We do not substitute the older Leumi formulation omitting c_f, a separable restriction, a fixed degree or polynomial, or a finite-n inequality.

## Existing mathematical bodies that already handle the easy routes

Theorem 1.3 supplies the conjectured asymptotic upper bound; Theorem 1.4 supplies lower bounds of the same order; Theorem 1.5 proves that the radical and LCM degrees are asymptotic. These do not determine the leading constant for every f. Theorem 1.8 already proves the complete limit for every irreducible *special* f: those for which f(X)-f(Y) is a product of linear factors over F_q[T]. Its Section 7 proof compares each evaluated linear factor's degree with a common prime's degree. Classification Theorem 1.10 identifies the special family. Rediscovering it would be routine and ineligible.

Most decisively, the actual Proposition 4.1 already makes the entire conjecture equivalent to S_f(n)=o(q^n), where S_f(n) counts distinct primes of degree greater than n+deg_T f_d dividing f(Q_1) and f(Q_2) for representatives with Q_1-Q_2 outside V_f. Its proof bounds the weighted excess multiplicity above and below by constants times n S_f(n). Proposition 4.2 bounds exact equal-value exceptional pairs by O(q^(n/2)), using the quantitative Hilbert irreducibility body stated in Lemma 4.3, with linear factors separately handled. Exact equality is weaker than sharing a prime; replacing the modular condition by equality is not justified. The Section 4 “random residues” calculation is explicitly heuristic, not a theorem establishing the needed uniform estimate. The main source itself provides the strongest concrete classical screen here. The cited Hilbert irreducibility original, Leumi thesis, and all citing literature were not exhaustively body-audited; no classical or novelty PASS is claimed.

## Sustained route analysis: large-prime collisions

First try a resultant. If H is outside V_f, irreducibility implies that f(X) and f(X+H) are coprime over F_q(T): otherwise equal-degree irreducible associates, having the same leading coefficient, would be equal. Thus their resultant is nonzero. A prime shared by f(Q), f(Q+H) divides this resultant. Its T degree grows O_f(1+deg H), so for deg H<n it has only O_f(1) distinct prime divisors of degree>n. But there are q^n possible H. Summing this bound produces only O_f(q^n), precisely the order that Proposition 4.1 already supplies, and not the required little-o. It also overcounts representatives. No independence between these resultant divisors and the low-degree root box has been proved.

To examine that failure concretely, use the diagnostic polynomial

    q=2, f(X)=X^3+X+T.

It is irreducible in F_2[T,X] since it is monic linear in T, with quotient isomorphic to F_2[X]. Its translation space is trivial (comparison of the X^2 coefficient gives H=0). It is not special: f(X)-f(Y)=(X+Y)(X^2+XY+Y^2+1), and the homogeneous conic X^2+XY+Y^2+Z^2 is smooth even over the algebraic closure (its gradient vanishes only at [0:0:1], which is not on it). Hence the conic has no linear factor, including over F_2(T). This is a diagnostic inside the ordinary domain, not a proposed partial-case outcome.

Put R=Q+H and G=Q^2+HQ+H^2+1. Direct expansion in characteristic two gives

    f(Q)+f(R)=H G,
    f(Q)+f(H)=(Q+H) G.

If Q and R are distinct monic degree-n polynomials and a prime P of degree>n divides both f(Q) and f(R), then 0!=H has degree<n, so it is invertible modulo P. Consequently P divides G and f(H). The three roots modulo P are Q, Q+H, H. The lower-degree third root supplies a useful exact reformulation, but does not show that the other two roots rarely lie in the degree-n monic box. At most three distinct large prime factors of f(H) is still only a constant bound per H; summation cannot yield little-o. Even solving this one cubic would not by itself resolve the full source target and would not qualify under the present brief.

The tempting stronger shortcut S_f(n)=0 for all f is already false. At n=4 the following exact control has a prime of degree 5:

    P=T^5+T^4+T^2+T+1,
    Q=T^4+T^2+T+1, R=T^4, H=T^2+T+1.

P divides both f(Q) and f(R), as well as f(H). This is a method obstruction, **not** a refutation of the source asymptotic. Finite experiments through n=9 exhibit S_f(n) equal to 0,0,0,1,3,3,8,12,25. These do not establish or contradict a limit.

## Exact capped controls

checks.py implements F_2[T] arithmetic using integer bits. All 65,536 pairs Q,R of degree at most 7 satisfy both displayed identities. All 52 encountered large-prime collision pairs through n=9 satisfy the lower-degree-root implications. Factor reconstruction checks every evaluated value; factor-max LCM degree independently agrees with incremental Euclidean-gcd LCM degree for all nine n. Prime generation uses repeated Frobenius and gcd tests, with exhaustive degrees through 13, sufficient for trial factors of the largest degree-27 values. Remainders left after trial factors are irreducible by the elementary degree bound. This independently compares two LCM computations, not two independent complete implementations of finite-field arithmetic.

Every Python/helper/heavy command uses the unchanged helper_guard.py (hash in provenance), with AS and sampled group RSS 512MiB, CPU210s, wall230s, nominal40ms and single BLAS/OpenMP threads. Exact checks completed in about 1.7s at sampled group RSS about15MiB. Finite checks are not an asymptotic proof. A constant count cutoff of twelve saved witness examples affects only illustrative examples, **not** the exhaustive checks or historical hit coverage. No cap was raised. No numerical floating-point sign is used.

## Public proof and chronology screen: deliberately not clearance

Current public searches for exact source title, authors, ID and function-field LCM resolution did not locate a matching complete proof body. The live MathDB record was retrieved, but its status is not novelty evidence. The author publication page was retrieved; neither that list nor search absence proves absence of follow-ups. Older integer LCM results and newer integer-only papers do not by title alone settle this fixed-q function-field statement.

Current head observations at 2026-10-29 23:50UTC: Omega 490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c (commit 23:46:41UTC), OpenAI 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a unchanged. A single fixed a19a578...→490f6bc... compare was retrieved; no subsequent HEAD chase. This does not repair r138's aa026...→a19a... **300-path cap**. The new response also requires explicit cap inspection (see registry-delta.json). HEAD commit file lists themselves return300 and are not complete trees. Cached qualified baseline path screens and inherited receipts remain path-level, not arbitrary theorem-body coverage. Two cached lexical ID hits occur inside blob hashes and are unrelated; no source theorem is inferred from them. No candidate-specific complete current registry-body clearance was achieved. This gate remains HOLD irrespective of the mathematics.

## Strongest objection, falsifier, remaining gap

The decisive objection is that no full ordinary proof or counterexample exists here. The resultant and cubic identities are classical elimination helpers; no helper or subcase receives credit. A precise mathematical falsifier, using Proposition 4.1, would be a fixed admissible q,f and epsilon>0 with S_f(n)>=epsilon q^n for an unbounded sequence of n, together with proof. One exceptional finite n cannot falsify the asymptotic. A complete prior theorem establishing the full limit would separately defeat novelty.

The remaining mathematical gap is a uniform-in-n collision estimate S_f(n)=o(q^n) for **each** fixed irreducible f, allowing inseparability and nontrivial translations, or a genuine asymptotic counterexample. Residue randomness, exact equal-value sparsity, squarefree-value control and the constant-per-resultant bound do not supply it. Full ordinary resolution, current target-specific proof-body screening, classical/substantive adjudication and independent investment clearance all remain before any Lean or manuscript work. Recommendation: **honest zero; unresolved**.
