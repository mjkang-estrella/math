# Analysis round 3

**Zero qualified discoveries, zero submissions, no formal implementation.** Four fresh literal records outside the previous 34 were examined: 325507, 347029, 374935, 352819, all congruent to 1 modulo 3. Actual primary target statements and their surrounding definitions were read for all four, together with three comparison bodies. Downloads are not claimed as complete line-by-line paper reviews. The strongest surviving target is 374935; its exact unpaid gap is below. No exhaustion is established.

The full-scope fast-regime CV inequality has an ordinary proof from an existing general theorem, recorded here explicitly so it is **excluded as routine**, rather than promoted for formalization. The trace polynomial counterexample is also excluded as an elementary negative-scalar sign defect. The exponential trace branch is unresolved. The hyperbolic question is publicly resolved.

## Context, reservations, and coverage

Read ancestor AGENTS, source upstream/catalogue, status, analysis and analysis-r2 REPORT/results, both independent REVIEW significance decisions, batch ledger/context, the other active campaign ledger and reservation metadata. Korn 329722 and Bessel 326635 remain excluded; neither was reopened. 381600/345816 remain parked; 369163 and all other accepted/in-review/submitted families remain excluded. The initial pool's 2,920 entries are routing metadata, not new technical coverage. Only four literal records and four primary target bodies count here.

`history-screen.json` hashes current ledgers/reservations and records no target-ID hits in the selected <=1.5MB report/review/status/ledger/result metadata. The original conservative exclusion index and sibling all-ref receipts were reused without copying their evidence trees. Fresh `git log --all` message and `git rev-list --all --objects` checks are in `registry-history.json`: 466,827 object/path lines, no target-topic commit-message hit. A genuine historical path exists for 352819 (`.../pi-algebra-discovery-r2/sources/352819-live.json`); its presence defeats any claim that this ID was never encountered. It was not pursued after finding the public exact resolution. Other raw six-digit regex hits in object hashes are not mathematical matches. This is a bounded path/message/history audit, not an all-ref semantic audit.

`reservation.json` was written at 03:36:29 UTC before primary mathematical analysis. Administrative timing caveat: parallel source downloads began at 03:36:17 while the freshness scan was finishing, 12 seconds before the reservation file was written. No proof work or body review preceded reservation. No competing reservation was found. Future rounds should write reservation before starting downloads too.

## 352819: excluded by an actual full-scope theorem

Le, arXiv:2112.01462v2, Conjecture 5.5, printed p11: P is real, homogeneous of degree k, symmetric and hyperbolic on R^n, and the matrix is in the paper's symmetric-matrix setting. If its eigenvalues belong to Γ(P), its diagonal does too and P(diag A)>=P(λ(A)). The corrupted database encoding is not used to enlarge the matrix class.

Teng Zhang, arXiv:2601.10602v1 (15 January 2026), **Theorem 2.12**, printed p6, proves both conclusions for every real symmetric A and symmetric polynomial hyperbolic with respect to the all-ones vector. Read the primary definitions, Theorem 2.10 and proof, and Theorem 2.12, rather than relying on the abstract. The mechanism is Schur–Horn majorization, Birkhoff permutation averaging, convexity of the hyperbolicity cone, and concavity of P^(1/k). This is the exact intended target. Source-scope discrepancies allowing nonsymmetric matrices would be wording defects and earn no credit. Exclude; no independent proof certification is claimed.

## 347029: complete ordinary reduction, excluded as routine

Degond–Herda–Mirrahimi, arXiv:2006.14985v2, (23)–(24), printed p11, and Conjecture 4.3, p12: for every δ>1, γ,p>0, the normalized density on r>0 is

    ρ_fast(r)=C r^(-2-δ) exp(-δ/r) (1+1/(γr))^(γpδ),

and CV(ρ_fast)<=1/sqrt(δ-1). The CV uses m0*m2/m1^2-1, so normalization cancels. Read also Lemma 4.2 and Appendix A.2's weaker Proposition A.6. No limit, integer-power restriction or extra δ>2 hypothesis is substituted.

The classical input was checked in **Fradelizi–Li–Madiman, arXiv:1512.01490v4, Proposition 3.2**, printed p6, including (11). If φ:[0,∞)->[0,∞) is integrable and log-concave, then

    H(z)= Γ(z)^(-1) ∫_0^∞ t^(z-1) φ(t)dt

is log-concave for every z>=0 (endpoint interpreted as in the paper). Monotonicity of φ is expressly unnecessary. This last detail matters: the function below need not decrease near zero. The actual statement, not an abstract, provides the subsumption screen.

Put a=γpδ and φ(t)=exp(-δt)(1+t/γ)^a. It is positive and continuous at zero, and

    (log φ)''(t)=-a/(γ+t)^2<0.

It is integrable because exponential decay dominates a fixed real power at infinity. For every z>0 its Mellin integral J(z) is finite: near zero φ is bounded and t^(z-1) is integrable, and at infinity the same exponential domination applies. The substitution t=1/r gives

    m_k(ρ_fast)=C J(δ+1-k),  k=0,1,2.

All three indices are positive since δ>1. Midpoint log-concavity at δ gives

    J(δ)^2/Γ(δ)^2 >= J(δ-1)J(δ+1)/(Γ(δ-1)Γ(δ+1)).

The Gamma recurrence, valid at these positive arguments, therefore yields

    m0*m2/m1^2 <= δ/(δ-1),
    CV(ρ_fast)^2 <= 1/(δ-1).

All quantities in the final square root are nonnegative; m1>0 and m2*m0>=m1² by Cauchy–Schwarz. Taking square roots proves the full conjecture. This is an ordinary proof relative to the stated published normalized-Mellin theorem. It is a direct change of variables and theorem substitution: **no substantive discovery credit and no Lean recommendation**. We did not locate an earlier paper announcing the named gene-expression conjecture as solved; that is distinct from the demonstrated routine subsumption.

`check_exact.py` additionally verifies 288 exact finite Gamma-sum cases with integer a, δ=2,...,9 and γ in {1/4,1,4}. These tests check the moment indexing and ratio orientation only; the all-real-parameter proof is above.

## 325507: elementary polynomial defect excluded; exponential gap remains

Paulin–Mackey–Tropp, arXiv:1305.0612v1, Conjecture 7.3, printed p17, quantifies over all Hermitian A,B,C, all positive integers q, s>0. It gives the signed positive/negative-part bounds recorded literally in `literal-records.json`. Read Lemmas 3.2/3.4 and the actual exponential-mean-value proof in Appendix B.3 as the targeted classical comparison. Those lemmas have unsplit squares and both endpoint weights; they do not imply the conjectured signed weights.

The polynomial assertion already fails in dimension one: A=-2, B=-1, C=-1, q=3, s=1 gives lhs=7 and rhs=3. This is independently exact in `check_exact.py`. It is an elementary scalar sign defect, not an eligible new mathematical mechanism, and does not resolve the exponential branch or the intended concentration extension. The initial floating searches found polynomial failures; they are retained only as diagnostics and superseded by this exact exclusion.

For the exponential branch define D=A-B and

    L=tr C(exp A-exp B),
    U=tr(D_+² exp A+D_-² exp B),
    V=tr(C_+² exp A+C_-² exp B).

The all-s assertion is equivalent, when U,V>0, to L<=sqrt(UV). Zero cases must also be handled in a proof. This is a useful precise optimization reduction, not a solution. `trace_search.py` tests 150,000 seeded real symmetric 2x2 triples using their explicit two-eigenvalue functional calculus; no positive gap was found. It is floating-point evidence and covers neither higher dimensions nor all Hermitian matrices.

The source's Duhamel/superoperator Cauchy–Schwarz proof yields the **unsplit** endpoint weights. Splitting D and C introduces cross terms with different left/right exponentials; their signs do not follow from spectral positivity of D_± and C_±. Thus simply dropping mixed-sign contributions is unjustified. The unpaid gap is a signed cross-term inequality for the genuine Duhamel operator, or a certified noncommuting witness. Next route: analyze the second variation near commuting scalar equality, retaining rotations of D's and C's spectral projections, rather than repeat unstructured finite scans. No exponential proof or witness is claimed. The publisher PDF returned403; no retry/bypass or substitute-body completeness claim was made.

## 374935: strongest surviving full-scope coefficient mechanism

Bérczi–Fehér, arXiv:2605.25271v1, **Conjecture 6.1**, printed p23: every partition λ with parts>=2, N=|λ|, M=|tilde λ|, every ceil(M/2)<=i<=M, and every r, must have

    C_(λ;i,r)=Δ_x^r P_(λ;i)(N)>=0,
    C_r²>=C_(r-1) C_(r+1),

with zeros outside the polynomial degree range. Read Section6 including the examples and Section6.1's exact admitted induction gap. Neither its top coefficient example nor Theorems5.2/5.4 on different Chern-class rows solve this statement. The real-rootedness shortcut is explicitly false in the body for λ=(3,3); the displayed cubic and coefficient-generating quartic have negative discriminants. The coefficients are external-parameter finite differences, not identified nef intersection numbers, so no automatic Khovanskii–Teissier/Lorentzian subsumption is asserted.

Read the underlying **Fehér–Juhász, arXiv:2312.06430v3, Theorem2.7**, printed p8, definitions and Examples2.9–2.10, and polynomiality Theorem4.1. Removing a largest part m, putting d'=d-m and e=e_m, the actual recursion is

    Y_λ(d)= (1/e) ∂( [Y_(λ')(d')]_(m/d') * ∏_(j=0)^(m-1)(j a+(d-j)b)),
    α_q(a,b)=α(a+qa,b+qa),  ∂α=(α(a,b)-α(b,a))/(b-a).

`plucker_exact.py` implements this operation over rational numbers at integer d>=N, extracts the genuine two-variable Schur coefficients, then takes exact forward differences in d. It reproduces the source rows (2,2), (2,2,2), (3,3) exactly. For all 76 partitions with 2<=N<=12 it checks 320 admissible rows: no negative coefficient or log-concavity failure, and the tested extra finite difference vanishes. This finite check does not prove a general degree bound or full-scope conjecture.

A stronger induction screen beyond real-rootedness is useful. One cannot apply the twisted recursion to **arbitrary** positive/log-concave binomial Schur rows and expect a polynomial positive transition. For example take artificial old class s_(2)=a²+ab+b², append m=4, and set t=d'=d-4. Its twist has leading term 48 a²/t². At t=0 the new product is 4b(a+3b)(2a+2b)(3a+b). Antisymmetrization and division by b-a leave, at (a,b)=(1,2), coefficient **-80640/t²** (before any positive multiplicity divisor). The nonzero pole is checked exactly in `check_exact.py`. Thus this artificial input does not even produce a polynomial in d. It is **not a counterexample** to the conjecture: the genuine geometric old rows satisfy additional cancellation/divisibility relations. It rules out an overbroad positivity-preservation induction based only on the separate rows' nonnegative log-concave coefficients.

The unpaid gap is to identify an invariant divisibility-compatible family of genuine Schur rows and prove its twisted divided-difference transition preserves the adjacent determinants **after summing across Schur indices**. Next concrete route: factor the compulsory falling-factorial divisors from each genuine row before deriving the finite-difference transition; retain coupled rows, since separate log-concavity does not survive arbitrary sums. A proof must show both cancellation and the cross-row synchronization. Neither is established here. This is potentially substantive if solved; the finite diagnostic and artificial pole obstruction earn zero discovery credit.

## Literal Lean feasibility and qualification limits

No Lean was written or built. No checked endpoint exists. An arithmetic certificate about supplied C-values would not formalize the Plücker conjecture. A literal endpoint needs λ as a finite partition of parts>=2; N and M from its actual sums; actual rational polynomials P from equivariant classes or a proved-equivalent recursion; C as iterated finite differences at N; and the universally quantified inequalities above. Theorem2.7's rational substitutions, exact polynomial cancellation, Schur-basis extraction and identification with the geometric class are all required bridges. The missing mathematical transition invariant remains missing in Lean too. No theorem about abstract arrays supplied with positivity hypotheses is proposed as a substitute.

For 347029, the literal density is a real-power function on Ioi0, normalized by its Lebesgue integral; moments are actual integrals and CV is their square-root ratio. Formal bridges include integrability at both endpoints for arbitrary positive real parameters, reciprocal substitution, normalized-Mellin log-concavity, Gamma recurrence and positive normalization. The published theorem has not been found as a checked Lean declaration here; importing it as an axiom is impermissible. This large classical bridge has no significance justification for formalization.

For the unresolved exponential trace branch, the endpoint must use actual matrix exponential and positive/negative parts from Hermitian spectral functional calculus, actual matrix trace, and arbitrary finite dimension. The two-eigenvalue diagnostic does not provide that endpoint. Neither an implementation budget nor availability of the necessary functional-calculus/sign-sensitive Duhamel lemmas has been established.

## Current public checks and source receipts

Receipts retain URLs, UTC times, HTTP status and SHA256. Source versions are visible in the PDFs: target versions 1305.0612v1, 2006.14985v2, 2605.25271v1, 2112.01462v2; comparisons 2601.10602v1, 1512.01490v4, 2312.06430v3. These are current public bodies retrieved in this round, not an assumption that an old abstract is current. Bounded live web searches covered exact titles, named conjectures, theorem subsumers, IDs and proof/refutation terms. No worldwide prior-art clearance is claimed.

Normal public repository pages observed openai/math head **4eaee87548250b2682affda7d05d947c05554bae**, matching the inherited complete listing; Omega dev head is now **73b75a73ab1f4273148f7b3f60e4d5ada0dc304a**, newer than the reused complete listing **5a97247bf6ad10485d8891db5430b9e34def4933** and the sibling observations. **Omega head delta remains HOLD.** An initially mistyped repository URL returned404; the corrected canonical repository page was fetched once. No GitHub API request was made. The inherited API rate limit and prior conjectures-site403 were respected without retry or bypass.

Reused complete path listings (174,506 openai entries, 7,598 Omega entries) and 572 inherited cached textual bodies in place; hashes and bounded searches are in `registry-history.json`. Routed path hits mostly concern unrelated Hadamard names; no target-specific path or cached-body match was found. This is neither full registry semantic coverage nor clearance of the Omega delta. Live MathDB API attempts for the four IDs each returned403; their current post/solution status is therefore **unverified**, and no retry or alternate-host route was used. Corpus open labels never serve as novelty evidence.

Reproduction: `python -I check_exact.py`, `python -I plucker_exact.py`, `python -I trace_search.py` from this directory. The first two use exact rational arithmetic; the third is explicitly noncertifying floating-point exploration. Source fetches were capped at15MB per PDF, timeouts40s, <=4 parallel fetches; diagnostics are bounded. Total lane size is small; inherited evidence is referenced, not recursively duplicated. All writes stayed in analysis-r3. No children, formal implementation, shared edits, commits, browser tabs, external messages, uploads, or submission occurred.
