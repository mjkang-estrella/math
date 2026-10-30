# Independent preliminary review: Fu–Li subunit Rényi threshold

Review date: 29 October2026. Candidate: sol-fresh-source-discovery-r111, supplied revision deefafeb6f. Scope is the complete ordinary counterexample, not a formal certificate or acceptance. Root alone adopts results. Counts remain8additional/38total; credit0.

| Gate | Verdict | Reason |
| --- | --- | --- |
| SOURCE | PASS | The official v3 primary text states the existential threshold with the intended iid log-concave scope; the candidate refutes that scope. |
| MATH | PASS | Normalization, convolution, tail identity, strict sign, all-real-order argument and cofinal witnesses survive independent derivation. |
| SUBSTANTIVE | PASS, scoped | A global obstruction to every subunit exponential-maximizing interval survives the actual closest bodies read. No complete classical bridge establishing that obstruction was found. This is not a literature-priority judgment. |
| NOVELTY | HOLD | Current registry semantic coverage and comprehensive historical coverage are incomplete. Bounded literature search found no exact prior resolution; it cannot certify absence. |

Recommendation: retain as an ordinary-math sound, provisionally substantive candidate, with novelty HOLD. Do not accept, count, start Lean, or prepare a paper on this review alone.

## Scope, instructions and freeze

Read ancestor and batch AGENTS, current NEXT, ledger and prior campaign context, source pin/catalogue instructions and root ADOPTION. Campaign excludes known proofs, routine corollaries, endpoint corrections and repeated families; no open-label or shortness inference is used here. MMPP and other parked families were not reopened. Work was solo, without children, git operations, shared edits, browsers, accounts, messages, posts or uploads.

The root freeze contains61 candidate paths. `audit.py` hashes each original in64KiB chunks. `before.json` records all61matches at2026-10-29T20:48:18.667770Z. PROOF.md equals ca72b385e83d919fbaa97af4d55f0e7d00e949c01c8c4af07fd93ef30fef977a. `after.json` records all61matching again at2026-10-29T20:52:43.350228Z; the guard exited0. This verifies filesystem agreement with the supplied manifest, not independent git-commit authentication; no git operation was used.

Mathematical/source core was copied to `inputs/`; copies of root primary receipts and official HTML were also retained. Four huge bulk files were streamed only for hashing, never duplicated, decompressed, concatenated or aggregated: required-hashes.jsonl39,611,695bytes; semantic-hits.jsonl191,486,103; inventory-content.jsonl.gz277,850,288; required-content.jsonl.gz528,007,260. Their hashes are in before/after and the copied root freeze. They remain originals outside this lane; no staging occurred.

All Python and rendering helpers ran through the unchanged guard: SHA256825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45; AS/groupRSS512MiB, CPU210s, wall230s, nominal40ms sampling, BLAS1. The exact check used9.6MB sampled RSS and exited0. No cap increase. Native bounded reads and apply_patch were used. An early combined context read produced truncated console output; no mathematical conclusion or exhaustive-coverage claim depends on it. Essential current context, primary sections and prior-family titles were subsequently read in bounded selections. Candidate failures (optional inventory termination, CMU404, invalidated provisional Maxwell/BNT freshness) remain preserved in copied provenance; none was silently repaired into a PASS.

## Source and interpretation

Official primary URLs: https://arxiv.org/abs/2510.09206 and https://arxiv.org/html/2510.09206v3 . Independently fetched HTTP200 on2026-10-29T20:48:46Z, matching root's20:45:55Z receipt hashes exactly. Abstract SHA256a71f98779e2b147eb3a0e4003ad8b29941786968ba9d9b947a065a206e1f8e5a; HTML5a6990b83ffa5f6bb348b6bc73da95d2fbd261307922f29f257ada7c7e8f1b87. Full URL/time/size receipts are `live-receipts.jsonl`.

Latest version displayed is v3,21July2026; v1 is10October2025 and v2 is27October2025. No journal-reference field or non-arXiv DOI is displayed in the inspected record. Search did not establish a journal successor; no journal publication or universal nonpublication claim is made.

Read the actual definition of log-concavity, (1.2), the following threshold paragraph, Theorem3.4 and Lemma3.7 with their proofs. The threshold is an attributed, explicit suspected assertion by Fu–Li, not numbered Shannon Conjecture1.1. Its existential p0 belongs to(0,1); exponential maximization is asserted for all p>=p0, with cube-uniform maximization below. Dimension1 already lies in the intended scope. The source does not require smoothness, strict positivity on all R, symmetry, or a fixed variance. An affine normalization would preserve the increment anyway.

Using the PDF skill, rendered and visually inspected actual printed page2 of the copied mirror PDF (source-page2.png). The paragraph and surrounding hypotheses agree with the official HTML. PDF SHA2560d55ebb3cf5f30ce30d3b0e00503b8240409bd1b54e80a920a170e6e418a4f65 came from https://borowiecki.dev/pdf/2510.09206 at20:35:47Z. Official HTML corroborates content, not mirror PDF byte identity. Search's indexed mirror text was older v2, reinforcing why indexed snippets were not used to authenticate v3.

The target is eligible as an explicit mathematical expert assertion despite lacking a number. The candidate disproves the whole proposed threshold, rather than correcting the equality convention at p0, identifying one isolated endpoint, or claiming actual optimizers. Nothing here resolves p=1 or the cube-uniform optimizer branch.

## Independent ordinary mathematics

For a>0 set c=(1-exp(-a))^-1 and f(x)=c exp(-x) on[0,a], zero elsewhere. The nonnegative measurable density integrates to1. Its potential x-log(c) on[0,a], +infinity outside, is convex and lower semicontinuous. Thus this is precisely source log-concavity including extended support. On the product probability space with density f(x)f(y), coordinate variables are independent and identically distributed. No dependent coupling is substituted.

For a sum value s, the allowable x interval is [0,a] intersect[s-a,s]. Its length is s on[0,a], 2a-s on[a,2a], zero otherwise. Therefore g(s)=c² exp(-s) times this length is the sum density. Integrating g gives c²(1-exp(-a))²=1, alternatively Tonelli applies to the product density. Endpoint choices are null sets. All relevant p-power integrals are strictly positive and finite: compact bounded f,g for finite a, and exponentially decaying x^p exp(-px) for the exponential sum, for every fixed p>0.

For 0<p<1 define J=integral_0^infinity exp(-ps)s^p ds, and Ja with s^p on[0,a] and (2a-s)^p on[a,2a]. Direct integration of f^p gives c^p(1-exp(-pa))/p, while that of g^p gives c^(2p)Ja. The increment is log(Ra)/(1-p), where Ra=c^p p Ja/(1-exp(-pa)). Rate1 exponential inputs give R=pJ. Same-rate exponential increments are invariant under common translation and nonzero scaling, so beating rate1 beats every one-dimensional exponential pair in the iid class.

Independently subtracting the two output integrals gives

    exp(pa)(J-Ja)
      = integral_0^infinity exp(-pu)[(a+u)^p-(a-u)_+^p] du.

This follows by shifting the missing tail s>a and subtracting the reflected part a<s<2a. Both tails are integrable; no subtraction of divergent integrals occurs. The integrand is nonnegative. Subadditivity at a-u and2u bounds its bracket by(2u)^p for u<=a; for u>a the same bound follows from a+u<=2u. For fixed u and a>2u, MVT bounds the bracket by2pu(a-u)^(p-1), which tends to0 because p<1. Exponential times(2u)^p is integrable, so dominated convergence proves exp(pa)(J-Ja)->0. Since J>0 this is eventually <J. Hence Ja>(1-exp(-pa))J, Ra>pJ (also c^p>1), and division by1-p preserves strictness. This proves the asserted every-fixed-real-p theorem.

A useful independent asymptotic sign check is log(Ra/R)/exp(-pa)->1: J-Ja=o(exp(-pa)), log(c)=O(exp(-a))=o(exp(-pa)), and -log(1-exp(-pa))/exp(-pa)->1. Thus the entropy improvement has leading term exp(-pa)/(1-p). No floating-point evaluation of that tiny term is a proof premise. These limits are fixed-p limits and provide no unjustified uniformity at p=1.

For p_n=1-1/n, a_n=2(48n)^n, n>=2, split the scaled deficit at u=a/2. MVT on the first piece bounds its integral by2(a/2)^(p-1)/p. The second piece has bracket<=(2u)^p<=2u there, and its integral is at most exp(-pa/2)((a+1)/p+2/p²), deliberately enlarged by1 in the integrand. At the cofinal values, the first bound is exactly1/[24(n-1)]<=1/24; a_n>=a_2=18432. The candidate's cubic exponential tail bound is valid. I used a different fourth-power certificate:

    exp(-a/4)(2a+10)
       <= 6144(2a+10)/a^4 <=18432/a^3 <=1/18432².

The first inequality follows from exp(t)>=t^4/24 and a>=10. Thus the scaled deficit is at most1/24+1/18432²<1/6, while J>=exp(-p)/(p+1)>1/6 (p<1 and exp(1)<3). This is a uniform elementary proof for all n>=2, not extrapolation from computed n. For every p0<1, Archimedean choice n>1/(1-p0) gives p_n>p0 and a finite counterexample. These witnesses negate any proposed threshold below1.

`check.py` is independent of the candidate checker. It performs245exact rational overlap checks by sorting interval endpoints and summing qualifying cells, and99exact cofinal arithmetic cases n2..100. It also verifies the single rational universal worst bound14155777/339738624<1/6. `checker-results.jsonl`, `check.log`, `check.guard.json` record success. Finite checks validate transcription/algebra; the analytic arguments above establish all p and n.

## Strongest falsifiers and classical bridge audit

The strongest immediate mathematical falsifier is lost normalization or the wrong logarithmic sign. Neither occurs. In Lemma3.7 the comparison exponential has rate c to match h_infinity(f), and its output entropy is an upper bound on ours. But its input entropy is also larger: h_p(f)-h_p(E_c)=log(c(1-exp(-pa)))/(1-p)<0. Two output entropies cannot be subtracted with a changing input entropy to bound their increments. Lemma3.7's proof transports one factor to the matched exponential, then applies Schur concavity; it proves no quantitative cancellation between these two slacks. Theorem3.4 combines decreasing rearrangement with that lemma only at infinity. The candidate's input denominator retains exactly the information those bounds omit. Source passage about general integrable functions is not used to relax the probability-mass requirement.

The strongest substantive falsifier would be a published theorem or completed classical first-variation argument for this same self-convolution ratio establishing that exponentials fail to maximize it throughout0<p<1. Shortness, familiarity of truncated exponentials, and generic localization machinery do not by themselves supply that bridge.

I read Melbourne–Tkocz, https://arxiv.org/abs/2005.10930 and retained PDF https://arxiv.org/pdf/2005.10930, actual Theorem6.1 and proof, Corollary6.2 and entropy comparisons. The live abstract200 at20:48:46Z lists only v1,21May2020; PDF SHA256d8accfde9efe110abf092b1d8951a9dee969b8650fa980943995e541cdbca2c4. Fu–Li cites the2021IEEE article (67,45–51); the arXiv theorem6.1 corresponds to its VI.1 notation, but I did not authenticate publisher bytes. The proof uses h_infinity(X-Y)=h_2(X), then entropy-order comparison. For orders>=2 it yields the sharp difference bound log2; for lower orders it gives a weaker dimension-dependent bound involving p^(1/(p-1)). This does not identify the sum optimizer or force a violation of exponential increment. Reflection turns sums to differences only for symmetric inputs, and these truncated exponentials are not symmetric. The p=2 identity cannot be continued as an equality at arbitrary p. Missing bridge: a strict lower improvement for the normalized sum ratio, not an upper entropy-comparison bound for a difference.

I followed the explicit truncated-exponential lead to Melbourne–Tkocz–Wyczesany, https://arxiv.org/pdf/2406.04200, v2 dated25January2025. Fetched20:49:23Z, HTTP200,229890bytes, SHA25694f9268daba8c9ecfd4cbf151fe0ec0396d5ff76786cb962e85f038916201a42. Read Theorem2, its localization proof setup and Remark14, Remark15, and Theorem8/16 with the section4 proof. Remark15's truncated-exponential observation concerns values of an even log-concave density at a fixed point under variance1, not entropy increments. The localization proof treats a linear point-evaluation functional with fixed variance, and addresses its strict-convexity caveat separately. It cannot be substituted into the nonlinear f-to-f*f ratio with its moving denominator. Section4 is an anti-concentration/forward Rényi power comparison for p>1 and smoothed independent sums. Missing steps remain both transfer to the different functional and the decisive strict subunit-order tail sign. This is no complete exclusion bridge.

Accordingly the candidate supplies a real surviving global obstruction, not merely an instance of either read theorem. Substantive PASS is scoped to this adversarial body comparison; unknown literature can still defeat novelty. The DCT/tail calculation is elementary, which remains the strongest reason to seek a precise historical first-variation counterpart before investment. No optimizer classification or additional product-dimension credit is warranted.

## Freshness, limits and feasible formal endpoint

`search-notes.md` lists all live bounded queries and relevant leads. `live-receipts.jsonl` and `closest-receipts.jsonl` preserve source times, hashes and404failures. Author URLs returning404 were not treated as unread-body clearance; the distinct official arXiv anti-concentration PDF succeeded. A web-open attempt repeated the404 for the anti-concentration author link; this was a404, not a bypass of a rate/access limit. No blocked registry endpoint was retried. No worldwide priority, exhaustive citing search, MathSciNet/zbMATH search or publisher VoR audit is claimed.

Known lawful Omega head remains89cda9c274d1122b7676173296af3047c3b64cd1 at supplied20:10:57Z; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. I inspected and hash-bound r108's cached short delta from73a5033dd654a16a14fcd1b13277f1a03d81d826. Its7commits touch3paths (two Fiedler/resistance documents, one nonbinary mutual-Abelian-border document); compare JSON SHA256c3995c03a58c7e1dcddd84d4685b1b90e2572b8bce831a70a3db3d83174a709f. `inputs/registry/`, `registry-receipts.json` and registry.log preserve this audit. Unrelated path names are not semantic absence evidence. Earlier HEAD/tree403 and300-file cap remain unresolved; no alternate API route or reset inference was attempted. The candidate's127827-file selected-text screen is broad but not a full semantic audit or a current registry refresh. These limitations keep NOVELTY atHOLD.

If root later clears eligibility/freshness, the literal formal target should quantify real0<p<1 and finite a>0, construct a probability law with the stated density, independent iid copies on its product measure, prove its log-concavity, all required integrability, actual convolution law and the strict entropy-increment inequality against an actual exponential iid pair. A second endpoint can express the explicit n witnesses and negate the existential threshold. Integral-ratio and tail identities are useful internal lemmas, but an endpoint assuming them or assuming the entropy transport is not the source result. The cofinal bound avoids DCT if only the full threshold negation is formalized; the every-real-p claim additionally needs a genuine limit or quantitative cutoff proof. No Lean code, imported unproved bridge, compile claim or investment estimate was produced here.

Root owns final adoption. Remaining blocker is evidence for bounded current/historical novelty, not an identified gap in the ordinary proof.
