# Independent preliminary review: normalized totient deficiency

Recommendation to root: exclude this candidate from substantive discovery credit as a routine classical consequence. Retain the valid ordinary proof uncounted. This is an advisory review, not an acceptance/counting action. No Lean or manuscript investment is recommended. Counts remain 9 additional / 39 total, next 40.

## SOURCE — qualified PASS for the asymptotic interpretation; full literal breadth not certified

The actual v1 PDF p18 Question 9.4 asks to determine the distribution of Δ(n)/φ(n), and predicts that this ratio tends to 1 in mean. Section 6 pp14–15 defines the same Δ and proves an unnormalized summatory expansion. The candidate uses exactly this Δ, including the harmless n=1 convention. The ratio is not a multiplicity function; Questions 9.1–9.3 are different problems.

The candidate completely proves the predicted convergence in mean, even in mean absolute error, and determines the limiting empirical law as δ₁. This is a natural and useful asymptotic answer to Question 9.4. The source does not specify a topology, probability model, rate, or normalization for fluctuations, nor explicitly say “limiting distribution.” Consequently I would label the outcome “mean convergence and limiting empirical distribution,” not an unqualified determination of the entire literal distribution question. No finite-cutoff law, fluctuation law, or pointwise theorem follows. Conversely there is no textual basis to require a finite-X exact law as the only acceptable meaning: ambiguity is a scope qualification, not a mathematical refutation. The candidate itself discloses this selected interpretation adequately.

## MATH — PASS

I independently checked the full PROOF.md, discovery.md, source Section 6 and final questions, and the checker's actual code. The proof does not use the source's unnormalized average as though division by φ were automatic.

For every m≥1 the product formula gives φ(m)²/m≥1/2, including the empty product at 1 and the worst factor 2¹. Thus A(Y)=Σ_{m≤Y}1/φ(m)≤√2 Σm^{-1/2}≤2√(2Y), and K=Σ1/(mφ(m))<∞. The integral comparison is valid also for noninteger Y≥1; for Y<1 the sum is empty.

The finite-sieve argument genuinely proves π(Y)/Y→0. For a fixed squarefree Q, counting coprime residue classes incurs an O(Q) error before taking Y→∞. Primes dividing Q contribute a fixed finite number. Inverse finite Euler products dominate the harmonic sum up to the prime cutoff, so their reciprocals tend to zero. No prime number theorem is hidden here.

Each pair (n,p|n) has a unique exact valuation a≥1 and coprime cofactor m; multiplicativity gives (p−1)/φ(n)=1/(p^{a−1}φ(m)). The a=1 majorant is exactly Σ_{m≤X} K_m [π(X/m)/(X/m)], where K_m=1/(mφ(m)); it is dominated by the summable sequence K_m. A finite-head/small-tail argument proves o(1), uniformly over all cofactors. Dropping coprimality is legitimate for positive terms. For a≥2 the bound is 2√(2X)Σ_p p^{-2}/(1−p^{-3/2})<6√X, using 1/(1−2^{-3/2})<2 and Σ_{j≥2}j^{-2}<1. The extended p,a sum is convergent; empty ranges cause no issue.

Since φ(n)>0 and S(n)≥0, R(n)<1 and |R(n)−1|=(1+S(n))/φ(n) exactly. This also handles n=1 (R=0), n=2 (R=−1), prime powers and the finitely many equality composites. For real X≥1, all sums run to N=⌊X⌋, and X/N→1. Markov's bound gives every positive epsilon, not just one diagnostic threshold. For t<1 use an error threshold smaller than 1−t; for t≥1 the empirical CDF is 1. Weak convergence follows at continuity points of δ₁. The asserted CDF value at t=1 is also true, although weak convergence alone would not require it.

The removed primes have count π(X)=o(X); the family 2p has count at most π(X/2)=o(X), and 1 is a singleton. Each retained domain therefore has cardinality X+o(X). Its nonnegative error sum is at most the full o(X) sum, giving the conditional mean, density and weak limits on composites and composites excluding 2p. Merely deleting a zero-density set would not preserve an arbitrary unbounded mean; positivity of the full error bound is the needed additional reason here. Along primes R(p)=−1/(p−1)→0, disproving pointwise convergence to 1.

## SUBSTANTIVE — FAIL for discovery-credit eligibility

This verdict is based on a complete applicable classical bridge, not shortness, familiarity, or a claimed exact prior publication. The actual Alladi–Erdős body pp275–285 proves the requisite unnormalized prime-support mean; its cofactor/tail architecture is explicit. More decisively, the following independent bridge turns that published result into the candidate endpoint using a fully proved generic totient moment estimate.

Write B(x)=Σ_{n≤x}S(n). Alladi–Erdős (1977), Theorem 1.1 and its corollary on p285, gives Σ A*(n) ~ (π²/12)x²/log x, where A*(n)=Σ_{p|n}p. Since 0≤S(n)≤A*(n), B(x)=O(x²/log x). Only this bound, rather than any unread expansion theorem, is needed. It is also explicitly supplied by the target Section 6 proof and Remark 6.2. Theorem 1.5 pp285–286 separately bounds repeated-prime contributions for their unnormalized A−A*; it is not silently used for our normalized terms.

First, S(n)≤n−1: expand Π_{p|n}(1+(p−1))≥1+Σ(p−1), then use Πp≤n. Put u(n)=S(n)/n∈[0,1]. Partial summation gives

Σ_{n≤X}u(n)=B(X)/X+∫₁ˣ B(t)/t² dt=O(X/log X).

For completeness, bound the integral below √X using B(t)≤t² and above √X using log t≥(log X)/2. The former is O(√X), the latter O(X/log X); finitely small t are harmless. Thus the averaged u² is also O(1/log X).

Next put v(n)=n/φ(n). Define g(1)=1, g(p)=(p/(p−1))²−1=(2p−1)/(p−1)², g(p^a)=0 for a≥2, and extend multiplicatively. Exact finite product expansion gives

v(n)²=Σ_{d|n}g(d).

All g≥0, and g(p)/p≤6/p² for every prime p≥2. Hence

(1/⌊X⌋)Σ_{n≤X}v(n)²
 ≤ (X/⌊X⌋)Σ_{d≥1}g(d)/d
 = (X/⌊X⌋)Π_p(1+g(p)/p)
 ≤ (X/⌊X⌋)exp(6Σ_{j≥2}j^{-2})=O(1).

The Euler identity is justified by increasing finite prime products with nonnegative coefficients; their uniform exponential bound proves convergence. This supplies the normalization control missing from the unnormalized mean alone.

Cauchy–Schwarz now gives

(1/⌊X⌋)Σ S(n)/φ(n)
 = average(u v) ≤ √(average(u²) average(v²))
 = O((log X)^{-1/2}).

Finally average(1/φ(n))=O(X^{-1/2}) by the elementary totient bound already proved above. Therefore average|R−1|→0. The Markov/CDF/restriction steps checked in MATH finish every claimed endpoint. This bridge covers all prime powers simultaneously, with no squarefree restriction and no exceptional-cofactor gap. It even supplies a nonoptimal rate, stated here only as a bridge consequence, not as a candidate fluctuation claim.

Thus the normalization is real extra reasoning, but its necessary uniform control is a generic positive divisor expansion and Cauchy–Schwarz applied to an actual classical mean. I do not find a substantive new arithmetic mechanism beyond that routine adaptation. The candidate's elementary cofactor proof is valid and self-contained; it is not necessary to assume the conclusion of a new normalized theorem to obtain the result.

Strongest countercase to my recommendation: the precise normalized limiting law is not explicitly stated in the inspected 1977 paper or in the source's proved theorems; the candidate resolves a newly posed expectation with an elementary proof avoiding PNT. “Routine” remains an eligibility judgment, not proof of prior exact publication. Its summable cofactor domination and all-exponent bound must not be dismissed merely for being short. Nevertheless the explicit independent moment bridge above establishes why those controls do not warrant discovery credit under this campaign's exclusion of routine corollaries. Root alone decides.

## NOVELTY — HOLD for priority; no literature-novelty PASS

Read actual cached source bodies: target Section 6 pp14–15 and Questions 9.1–9.4 pp17–18; Alladi–Erdős introduction, Theorem 1.1 proof and corollary, Lemmas 1.2–1.4, Theorems 1.5–1.7, and remaining Sections 2–3 pp287–294 at text-body level. Scanned mathematical OCR is imperfect: I do not certify every glyph of unrelated formulas in Sections 2–3. The positive mean statement/corollary and cofactor architecture used above are readable and also corroborated explicitly by target Section 6. No literal normalized-deficiency endpoint was identified in that body. Lemma 1.4's proof is omitted in the original, not supplied by my reading.

Alladi–Erdős: received 1975-10-29, revised 1976-10-29; volume 71(2), December 1977, pp275–294. Target: arXiv2610.36260v1 submitted 2026-10-26 20:37:43 UTC, title page 2026-10-23, only v1 listed on freshly retrieved abs page. No journal version authenticated. Exact URLs, UTC retrieval times, source bytes and SHA256 are preserved in copies/http.jsonl and http.jsonl. The live abstract and versioned HTML are byte-identical to the author's cached bodies. The cached PDF and HTML remain separate because bibliography formatting/numbering differs; PDF controls page labels.

Bounded fresh search on 2026-10-30 UTC: arXiv all-fields “totient deficiency” returns the target and Defant's different Schemmel-iterate paper. This is narrow metadata coverage, not a full-text/citing survey. Fresh registry download is byte-identical to the inherited September catalog: commit c74ecadd, generated 2026-09-09 17:22 UTC. Exact source id/author aliases absent; generic totient/deficiency hits do not identify this endpoint. This is NOT an authenticated current full registry head and cannot clear live proof history.

Bateman1972, De Koninck–Ivić1984, and Ranjan–Singh2026 actual bodies remain unread. The latter is listed as to appear by the source; no separate publication date authenticated. No absence inferred from these gaps. Original r199 qualified-history result covers 1,511 designated records only, not all history; this review does not re-run or expand its parked intervals. Seven r111–113 original-report preservation claims remain inherited, not independently re-audited here. Administrative ledger/prior-context snapshots were read; their accepted, excluded and held families remain excluded from any fresh credit claim. No denied GitHub/ScienceDirect/Google route attempted, no browser, no retries or bypasses. Current bounded search cannot clear all history or establish worldwide priority.

## FORMAL-FEASIBILITY — feasible in principle, unverified and not recommended for investment

The proof uses finite prime-support sums, multiplicativity of φ, elementary sieve counting, convergent series and density/measure limits. It appears formalizable but would require substantial analytic and number-theoretic plumbing. No Lean file was created, inspected as a certificate or compiled; no literal formal endpoint or axiom audit exists. This is neither a formal PASS nor grounds to spend resources after substantive FAIL.

## Diagnostics, custody and procedural limits

Own independent_checker.py uses direct gcd counting for φ and trial division for prime support, rather than the candidate's sieve/cofactor checker. It verifies 2,500 exact rational error, product-expansion and Cauchy controls, including small integers and half-integer cutoff floors. It passes. A private replay of the candidate's unchanged checks.py passes 10,000 exact decomposition controls. Both are finite diagnostics only, never the proof of the universal limit.

Scientific originals were hashed, copied privately and immediately rechecked in freeze-before.json. freeze-after.json and the separate final verification check those same original paths and private copies without rebinding. Candidate root decision was read only as mutable administrative direction, not frozen as scientific evidence. NEXT/ledger/prior-context are snapshots only and live mutable files are not compared as scientific inputs. No shared write, MathDB edit, git operation, external message/post/upload, Lean/manuscript work or child agent was performed.

One initial unguarded pwd/rg inventory violated the all-helper guard requirement; broad output was truncated. This is preserved as a failure, not retroactively cured. Subsequent helper/Python/retrieval/write/hash commands used the designated guard with required environment and unchanged AS/RSS512MiB, CPU210s, wall230s limits. Early oversized read output was truncated; focused source-body reads supplied the passages relied upon. Final manifest explicitly excludes itself and verification-receipt.json. The latter is generated by a separate guarded invocation after all final packet writes.
