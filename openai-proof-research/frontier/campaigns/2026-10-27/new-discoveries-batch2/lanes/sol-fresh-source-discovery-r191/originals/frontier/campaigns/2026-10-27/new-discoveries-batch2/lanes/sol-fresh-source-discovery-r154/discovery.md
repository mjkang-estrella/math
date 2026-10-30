# Source research r154: weighted Bernoulli tail, unresolved

Solo assigned-lane research. No nomination or complete ordinary result. Actual retrieval timestamps are 30 October 2026 UTC (29 October Pacific); source dates are recorded separately.

## Freshness before download

The original r151 history receipt is the qualified base (inheriting r148/r147/r145). `history-delta.json` binds it by hash and records only changed/new immediate original batch SUMMARY/discovery/PROOF/review/DECISION roles and missing paths. No global date cutoff, giant replacement inventory, or omission of the original r111–r113 science. Each alias query read the complete original body, with an exact-hash check, and preserved matching bodies under reopened/. These are 1,633 role-qualified bodies, not 1,633 independent results or a semantic completeness claim. Inherited duplicate copies in the qualified base are not new evidence. No generated inventory/search echo was added to the original-role index.

Before retrieval queried source ID, exact title, author spellings, and aliases including weighted Bernoulli, sum exceeds mean, Sudakov and Manickam–Miklós–Singhi. The sole original match was structural-r176-contribution-r1/REVIEW.md: its actual opening comparison concerns Conlon–Fox–Sudakov cycle constructions and polynomial graph algorithms, not this probability assertion. It was reopened and scope-compared. No exact prior selected-family pursuit appeared in the qualified bodies. This supports provisional freshness only.

Earlier leads were stopped: actual r47/r129 reports identify Gaussian Radon prescribed-split log-concavity as old; r116 identifies Matkowski's full paranorm convexity question as old; r106 identifies Kunisky's Gaussian-minimum and equal-zone-volume questions as old. No new source download or sustained mathematics for these. Javaheri's revised arrangement question likewise has an actual public refutation documented in the reopened original r22; it was stopped. Author-name overlaps with the credited gamma family or old quasi-additive Matkowski equation are distinguished in those original reports. No old family is rebadged.

## Exact latest source and closest actual bodies

Aleksa Milojević and Benny Sudakov, *On the Probability a Weighted Bernoulli Sum Exceeds Its Mean*, arXiv:2606.30287v1, submitted 29 June 2026 13:28:12 UTC. Current abs history lists v1 only; unversioned and v1 PDFs downloaded independently have identical SHA256. No journal reference was found on that actual abs page; no comprehensive journal search or equality with a hypothetical published version is claimed.

Read the full four-page source, especially Conjecture 1 (p1), restricted Conjecture 3 and Theorem 4 (p2), Claims 5–6 and limiting argument (pp2–3), Proposition 7 (p3), Samuels discussion and references (pp3–4). Literal full target: for every integer m≥1, every w∈(0,∞)^m with Σwᵢ=1, every real p∈[0,1/3], and independent vᵢ with P(vᵢ=1)=p, prove P(Σwᵢvᵢ≥p)≥p. Zero weights may be deleted. The weak event ≥, all real p, and unbounded m matter. No equal-weight, reciprocal-p, or small-p instance resolves it.

Theorem 4 is conditional on the restricted MMS statement: random independent color assignments produce at most m nonnegative centered row loads, all negative row loads equal, and conditional sampling of k colors has exactly the required iid Bernoulli marginal law. It does NOT prove restricted MMS. For arbitrary fixed m, growing n makes 1/n smaller than the least weight, but does not remove that missing combinatorial inequality. Its p≤10^-46 statement uses Pokrovskiy's external theorem; the Pokrovskiy body was not audited here and is not used for a new deduction or full exclusion.

Followed the CURRENT actual source-facing First Proof report link before sustained mathematics. Read report §§3.3/5.3 and extracted its actual hyperlink to submission-3A-reviews.pdf using Poppler. The linked GitHub repository was read at observed head 274625a22e4748d5f9264ba3614353461520bd20, commit 17 August 2026 03:33:23 UTC. The full untruncated tree agrees with that commit. Retrieved actual immutable human-solution.tex, submission-A.tex and review PDF. Read the human coupling proof and AI coloring/pairing, closure, equivalent forms and obstruction proofs; the review's opening distinction and annotated mathematics explicitly retain the all-p≤1/3 gap. Its June4–8 review dates, June29 source date and August17 archive-head date are different chronology facts; no original upload date is inferred from archive HEAD.

Submission A already proves p=2/b (b≥6), reciprocal cases and multiplicative/closedness properties, and explicitly records cyclic-count and pair-coalescence obstructions. These are public partial mathematics, not our discoveries. Its seven 1/7 plus three zero loads give 35<36 heavy triples at p=3/10, invalidating a naive pointwise MMS strengthening. The source's asymptotic bounded-nonnegative/equal-negative restricted conjecture is different from that false finite strengthening.

Actual published companion: Fokkink–Meester–Pelekis, *Optimizing stakes in simultaneous bets*, ALEA20 (2023),153–165, DOI10.30757/ALEA.v20-07. Read definitions/Conjecture1.1, Proposition3.2 moment proof, Theorem4.4, Theorem5.1/Corollaries5.2–5.4, and Theorem6.1 proof. They maximize an upper tail with t≥p. Theorem6.1 requires p<1/(2k+1), t>1/(k+1); it does not reach the diagonal with the needed strict complementary-event endpoint. Complementing our event gives P(ΣwᵢBerᵢ(q)>q)≤q, q=1-p≥2/3. Replacing >q by ≥q changes atom contributions. The favorable-odds off-diagonal results and conjectured stability do not supply a complete bridge. No classical exclusion is asserted.

The original MSE question was attempted once by HTTP and returned403; stopped. The web reader showed its reciprocal coupling and two p>1/3 counterexamples, not a full small-p proof. Those web-read comments are not a locally archived primary proof or novelty clearance. The guessed Princeton author page returned403 and stopped; the ETH papers.html route returned404. No challenges were bypassed. The actual human/AI proof bodies above are available independently.

## Sustained attack: exact parameter chambers

For an integer positive vector a=(a₁,…,a_m), D=Σaᵢ, let

H(s,k)=#{A⊆[m]: Σᵢ∈A aᵢ=s, |A|=k}.

Multiplication of ∏ᵢ(1+u z^{aᵢ}) gives an exact bounded dynamic program for H. For parameter p in (s/D,(s+1)/D], the good event is the fixed family with integer weight ≥s+1. Put C_k=Σ_{t≥s+1}H(t,k). The exact defect is

G_s(p)=Σ_{k=0}^m C_k p^k(1-p)^{m-k}−p.

In degree-m Bernstein basis B_{k,m}(p)=binom(m,k)p^k(1-p)^{m-k}, its coefficients are b_k=C_k/binom(m,k)−k/m. Affine restriction to [s/D,min((s+1)/D,1/3)] is computed exactly with rational de Casteljau interpolation. Nonnegative restricted coefficients prove G_s≥0 on that closed interval, since the basis is nonnegative and sums to1. At the left endpoint the selected event may omit an equality atom; that only makes this a stronger lower bound than needed. Adjacent chambers cover all positive parameters through1/3; p=0 is immediate. Thus endpoint conventions are preserved.

The checker enumerates every nondecreasing positive integer partition with total1..18 and length1..7. All 6,120 nonempty chambers for the resulting1,176 vectors pass directly; no bisection is needed. A separate 2^m subset enumeration at p=3/10 validates each DP evaluation, so the DP is not checked only against itself. This is a reproducible finite collection of real-parameter certificates, NOT an all-dimension or all-weight proof. Permutation symmetry and repeated rational representations earn no separate credit.

The attempted uniform Bernstein-sign route stops here. For arbitrary dimension and arbitrary weight chambers, no coefficient lower bound has been proved. In particular the restricted first coefficient is the right-limit defect at a subset-sum threshold, so declaring it nonnegative universally simply assumes a substantial piece of the original conjecture. A finite grid cannot establish such a lemma.

Passing from an unbounded rational family to real weights would be possible: approximate a real probability vector by positive rational vectors. For each subset strictly below p, its gap remains positive under sufficiently close approximation, while subsets exactly at p can only help the target event in the limit. Finite product probabilities then give P_w(X≥p)≥limsup P_{w_n}(X_n≥p). However the required rational theorem for all denominators and all m is absent; our finite grid is not a dense family in every dimension.

## Coupling and induction checks, with actual objections

An independently derived positive-load variant of the public cyclic obstruction uses p=2/7 and cyclic loads a=(3,1,3,1,3,1,3)/15. The seven length2 sums are2/5 once and4/15 six times; only one exceeds2/7, fewer than the desired two. This disproves the proposed deterministic cyclic interval lemma even with every load positive. It does not refute the averaged random-coloring inequality. Its actual iid Bernoulli probability is334168/823543>2/7. Submission A already records the same obstruction mechanism with zero loads; no new result claimed.

For pair merging, writing T(x)=P(R≥x), a,b>0, direct conditioning yields

P(R+aB+bC≥p)−P(R+(a+b)B≥p)
=p(1-p)[T(p-a)+T(p-b)−T(p)−T(p-a-b)].

There is no uniform sign. More decisively, the actual public draft's capped equal-weight example p=3/10,w=(1/4)^4 has original tail3483/10000; merging ANY pair gives363/1000, a larger tail. Thus no “some pair decreases the tail until a dictator” induction exists in this form. Reproduced exactly, uncredited. The draft's general equal-weight obstruction covers whole reciprocal chambers. Larger/adaptive blocks might work only with a new uniform alternative bound; full collapse alone is equivalent to comparing the unknown original probability with p.

## Strongest objection, falsifier, and precise gap

Strongest objection: every tempting dimension-reduction/coupling result so far either reproduces an actual public partial argument, fails on an exact public load example, or restates the unknown universal lower bound. The chamber method is an exact finite checking device and offers no demonstrated uniform sign mechanism. No result is nominated as nonroutine.

A genuine source falsifier would be an actual finite positive vector w and p≤1/3 with an exact or rigorously bounded probability strictly smaller than p. Negative Bernstein coefficients alone would only defeat that sufficient test; cyclic load failures and negative merge gains only defeat methods. None is a source counterexample here.

The remaining mathematical gap is P(ΣwᵢBerᵢ(p)≥p)≥p for arbitrary finite m, arbitrary real positive probability vectors, and every real p≤1/3 outside already-public cases. No complete ordinary proof or counterexample exists in this lane, so no PROOF.md.

## Registry and coverage limits

Fixed Omega490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c root fetched once. Its Library/Problems/docs IDs agree exactly with the retained untruncated r143 scoped trees; reuse is hash-bound in registry-scoped.json. Selected source/author/claim-alias path screen returns no exact resolution. Generic Bernoulli-polynomial, quantum-walk and leakage names are not exact same-object proofs and were not treated as exclusions. Complete baseline gzip listings were streamed under guard for targeted path leads, with compressed/uncompressed hashes in registry-paths.json. Fixed OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a is preserved; unrelated Bernoulli-convolution and Bernoulli free-boundary manuscripts are not this claim.

The aa026→a19a and a19a→490f comparison lists remain capped300. The reused baseline and narrow scopes do NOT clear all changed bodies, later aliases, other registry locations or worldwide literature. No HEAD chasing, public Lean replay, global novelty PASS, unread-abstract proof assertion or universal priority claim. Bibliographic title searches were bounded; no MathSciNet/zbMATH sweep or complete citer audit. First Proof's actual source-facing links, rather than a registry path absence, supply the decisive public partial-math comparison.

All Python, retrieval/conversion and finalization scripts run under the unchanged assigned helper guard with BLAS1, AS512MiB, sampled groupRSS512MiB/CPU210s/wall230s, nominal40ms. Group sampling can miss subinterval spikes; no stronger peak guarantee claimed. Missing fitz and pypdf imports failed without cap changes; preserved in failures.md/report-links.log, then native Poppler link extraction succeeded. No Lean or paper investment.
