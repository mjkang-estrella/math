# r38: fresh-source screen and incomplete Baxter attempt

Disposition: NO FULL RESULT. No nomination, count authority, acceptance, paper, PROOF.md or Lean certificate. All classical observations below are uncredited. Only the assigned lane was written.

## Source screen

1. Ambrus–Gárgyán, *Estimates on the decay of the Laplace–Pólya integral*, BLMS 57(11), 2025, 3360–3379, DOI10.1112/blms.70157. Authentic published PDF, internal pp16–18, Eq4.2–4.11 and final conjecture; pp17–18 rendered and inspected. Current arXiv2412.12835 lists v3, revised13July2025. Fresh to the searched previous-lane summaries, but EXCLUDED as an immediate same-source classical-bound corollary (details below). This is not a substantive new outcome.
2. Sun, arXiv2505.02767v4, published2026, rising-binomial q-log-convexity assertion. The current MathDB368293 actual solution body gives both the existing m5,n7 obstruction and a posted all-m>=4 argument. Do not rediscover its refutation; m2/3 and the separate double-sum polynomials are not excluded wholesale. The posted body is prior evidence, not externally certified mathematics. The guessed MathOverflow URL in http.json failed404; the actual URL in the saved MathDB body is questions/479301. No bypass/retry was attempted.
3. Banerjee–Kundu, *On an irreducibility question concerning palindromic non-cyclotomic 0,1-polynomials*, Integers24 A71(2024). Actual pp1–5: Conjecture1 asks that every irreducible reciprocal non-cyclotomic 0,1 polynomial f have f(x^r) irreducible for every integer r>=1. Source only settles fewer than15 terms for r2. Capelli's general criterion does not furnish a plausible complete elimination of power roots in this class. Screened out before computation; no bounded coefficient search presented as progress. The x monomial issue in broader Question1 is already explicitly discussed in the source and is no discovery.
4. Selected target: Fang–Zhang–Zhao, arXiv2505.05873v1, Conjecture4.2. Current arXiv lists only v1; published JMAA561(1)(2026)130615 DOI10.1016/j.jmaa.2026.130615. Actual published full body HTTP403: published-version eligibility HOLD. Do not infer exact latest-published conjecture identity merely from matching abstract. The preprint conjecture is precise and genuinely fresh relative to the searched lane exclusions, but no full solution was reached.

## Exact selected question and quantifiers

For every integer n>=1 let

B_n = sum_{k=1}^n 2 binom(n+1,k-1) binom(n+1,k) binom(n+1,k+1) / (n(n+1)^2).

For any sequence a indexed by n>=1 define (L a)_n=a_n a_{n+2}-a_{n+1}^2; L^0 a=a and L^{r+1}a=L(L^r a). Conjecture4.2 asserts

**For all integers r>=1 and all integers n>=1, (L^r B)_n>=0.**

This is the full Baxter target, not Conjecture4.3's extension in the Hoggatt parameter and not the weaker assertion that for each fixed r there exists N_r such that all n>=N_r work. The source proves that eventual statement and 2-log-convexity. Actual definition(1.1), source pp2–4, Section3 pp8–10, Section4 pp10–11 were consulted.

## Current primary/public-body screen

Current source arXiv metadata, live MathDB368344 body, current named repository heads and the complete current Omega D5 and Problems subtrees were obtained before sustained investment. Empty MathDB solutions are not novelty evidence. The source's own negative Hankel observation defeats the standard Stieltjes-moment theorem. Two current related primary papers were retrieved and their actual closest bodies read:

* Liu–Mao arXiv2608.22258, pp17–18 Theorem5.1 and proof setup, pp29–31 Theorem6.1 and proof. They prove coefficientwise FIRST log-convexity of Baxter polynomials and a linear transformation preserving log-convexity. Neither statement asserts closure under iterated nonlinear L. Substituting the constant input into a log-convexity-preserving transform gives only the first L inequality. An all-order representation of L^r B as repeated outputs of that transform was not found.
* Mao–Shi arXiv2607.01582, pp16–17 Eq6.1, Theorem6.1 and Proposition6.2 proof: a three-term-recurrence criterion yields first log-convexity. Their infinite log-CONCAVITY results for rows/columns are different statements from infinite log-CONVEXITY of row sums. Index B_0=1,B_1=2 there corresponds to the selected source's B_1=1,B_2=2.

Nearest registry body WeakAscentSemiBaxter.lean proves equinumerosity for semi-Baxter avoiders, not iterated positivity. SincSquareDerivativeBudget.lean defines an entire cosine-square-root profile and bounds derivatives; it is not the Laplace–Pólya sequence question. Neither external file was kernel-replayed. Filename screening does not exclude differently named subsumers. Complete current D5/Problems retrieval supersedes the truncated compare; no claim of whole-dev completeness or novelty PASS.

## Full-route attempt and exact failure

The initial plausible complete route was to represent B as a Stieltjes moment sequence and invoke the classical preservation theorem under L. This would cover every r in one argument. The source already warns against it. Exact checks reproduce det(B_{i+j})_{0<=i,j<5}=-616 when B_0=1 is appended. More decisively for the literal n>=1 sequence, det(B_{i+j+2})_{0<=i,j<6}=-115894592. A Stieltjes representation B_{n+1}=integral x^n dmu would make this shifted matrix positive semidefinite. Thus that representation is impossible. No replacement positive representing object was obtained. This negative determinant does NOT refute infinite log-convexity, which is weaker.

Second route: propagate an invariant cone through the exact recurrence

(n+4)(n+5)B_{n+2}=(7n^2+35n+40)B_{n+1}+8n(n+1)B_n.

Put a_1=1,a_2=t and continue this recurrence. Then

a_3=(41t+8)/15, a_4=(1063t+184)/105, a_5=(31082t+5456)/735.

Writing c_i=a_i a_{i+2}-a_{i+1}^2 gives

c_1=-t^2+41t/15+8/15,
c_2=(4178t^2-1832t)/1575-64/225,
c_3=(48131t^2+27056t)/3675+1088/1225.

But

c_1 c_3-c_2^2=-(41t+8)(1218149t^3-2331519t^2-1140912t-121792)/2480625.

At t=117/50 all three c_i are positive, while c_1 c_3-c_2^2=-32503777888039/15503906250000<0. Thus local first-order positivity plus the exact recurrence is insufficient for induction under L. The actual Baxter initial ratio is t=2, so this is a ROUTE obstruction, not a source counterexample. A global all-n condition stronger than these three inequalities might still succeed; it was not established here.

Iterating polynomial expressions in t gives degree2^r and loses the order-two linear recurrence. A full cone theorem controlling those expressions at every n,r, or another positive combinatorial interpretation of L^r B, is the exact unresolved bridge. No induction on r with such a preserved class was proved. The existing eventual-r result does not supply it: modifying finitely many starting values leaves all eventual statements true while possibly breaking an early L inequality.

Exact capped probes (integers only): B_1..B_64, r1..12 with n<=64-2r; and B_1..B_36, r1..16 with n<=36-2r. All computed L entries were positive. This is neither a proof nor a reason to claim the conjecture. Check.py independently compares the binomial formula with the published recurrence for64 terms and verifies both Hankel and recurrence obstructions.

## Strongest adversarial objection and falsifier

The proposed positive-moment proof is impossible in its stated form, and the next recurrence induction is missing its essential invariant. The natural monotonicity-preserving linear transform from current followup work is not a nonlinear-L preserving theorem. No theorem here implies the requested all-order, all-index positivity. A single exact negative (L^r B)_n for any n,r>=1 would fully refute the preprint claim, provided independently checked against its literal definition; none was found. Conversely finite positivity through r16 cannot answer universal r. Published source comparison remains HOLD regardless of these mathematical gaps.

## Ambrus classical exclusion bridge (uncredited)

Use f(m)=max_l A(m,l)/m! as defined in Eq4.5–4.7, not the inconsistent printed Table3. For the subsequence starting at p2, the target inequalities have midpoint p>=3. Theorem4.2 quotes Lesieur–Nicolas1992; Eq4.10 converts its bounds to

L(p)=2p^2/(2p^2+p-1) < f(2p)/f(2p-2) < U(p)=p(2p+1)^2/[2(p+1)^2(2p-1)].

Then

L(p+1)/U(p)-1=(2p^3-5p^2-10p-4)/[p(p+2)(2p+1)^3].

For p=4+u,u>=0 the numerator is 2u^3+19u^2+46u+4>0. This proves the source's log-convexity inequality for every midpoint p>=4 directly from its quoted classical theorem. The remaining p3 is exact:

f(4)=11/24, f(6)=151/360, f(8)=15619/40320,
f(4)f(8)-f(6)^2=23423/14515200>0.

Two independent exact Eulerian constructions (recurrence and Eq4.2 finite alternating sum) agree. The published Table3 instead prints f4=23/48 and f6=841/1920; these do not agree with the defining Eulerian quantities or Eq4.10. No repair of that table is proposed or counted. Original1992 body not retrieved: initial incorrect NUMDAM guessed URL404 and actual publisher403 recorded. The exclusion relies on the explicit classical theorem as quoted in the authentic2025 body, not a claim to have read the1992 proof or found a public explicit resolution. This short same-source consequence is unsuitable for substantive discovery credit even if no separately published solution is located.

## Lean disposition

No Lean work started. With no complete ordinary Baxter proof and a published-source HOLD, there is no justified literal certifiable endpoint yet. A future endpoint would define the exact finite binomial sum in rationals, recursive L, and prove `∀ r n : ℕ, 1 ≤ r → 1 ≤ n → 0 ≤ iterateL r sourceB n`. It cannot replace sourceB with an assumed positive-moment model or assume the cone/invariant being sought. No feasibility PASS or compile claim. If revived after ordinary proof and eligibility review, the required pin is Lean4.34.1/mathlibd13f23b723b8a846827a245b89c10fc7d3f11612, strict std3 and serial process limits as instructed. The Ambrus routine corollary is not a formalization target for discovery.
