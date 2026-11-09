# 324571 — ordinary proof proposal, zero credit

Exact target: the full literal in literal-provenance.json, ID 324571, asks sup_p D(p,p)<1. No restriction to finite support, a fixed number of colors, or a special one-parameter family is imposed. The probability model is paid by the actual final primary body: Arratia–DeSalvo, Advances in Applied Probability 47 (2015), 292–305, DOI 10.1239/aap/1427814592, Section 9.1 pp.302–303 and Section 9.2 Conjecture 4, equation (19), p.304. Acquired final PDF SHA256 728f08ab1ce93181dd2f0fc465d7b524b216a1da0b006cfce8765c57f1760ef8. Distinct original arXiv1211.6486v2 also read at Sections 2–4 and 9. The final keeps the conjecture, and its Theorem 3 proves only a special limiting-family formula. We do not infer the desired uniform bound from that formula.

## Precise proposed theorem
For every discrete probability distribution p, under the independent draws and alternating left/right stopping rule of Section 9.1,

    D(p,p) <= 255/256.

In fact the sequential winning-color law dominates 1/256 times the conditional pair-color law pointwise. This resolves precisely Conjecture 4 if the proof below survives independent scrutiny; it does not determine the optimal constant or resolve Conjecture 5.

Represent the countable support by N (a finite law extends by zero). Put s=sum_i p_i^2. Then 0<s<=1 and p_i<=sqrt(s) for all i. Let L_1,R_1,L_2,R_2,... be independent, each with distribution p. Continue the sequence forever even after a match. Let Y be the color of the first left/right match in this chronological order, and let X be the color of an independent left/right pair conditional on equality. Then x_i=P(X=i)=p_i^2/s. For every N, no chronological match through 2N implies L_j != R_j for all j<=N, an event of probability (1-s)^N. Thus the first match exists almost surely; y_i=P(Y=i) sums to one. No finite-support compactness argument or continuity assertion is needed.

## Full ordinary proof
If s>=1/64, the event L_1=R_1=i already forces Y=i, so y_i>=p_i^2=s x_i>=x_i/64>=x_i/256. This includes point masses and all other large-s laws.

Suppose now 0<s<1/64. Let K=floor(1/(4 sqrt(s))). The real number being floored exceeds 2. Consequently

    1/(8 sqrt(s)) <= K <= 1/(4 sqrt(s)),
    K^2 >= 1/(64s),      K^2 s <= 1/16.

Fix i. If p_i=0 the desired lower bound is trivial. Otherwise p_i<=sqrt(s)<1/8, so 1-p_i>7/8 and K p_i<=1/4.

For 1<=a,b<=K, define E_ab to be the event that among the first K left draws exactly L_a has color i, and among the first K right draws exactly R_b has color i. These K^2 events are disjoint. Their common probability is p_i^2(1-p_i)^(2K-2).

Conditional on E_ab, every other left/right draw is independent with law p_j/(1-p_i) on j!=i; the conditioning is a product of coordinate conditions. For each pair of such other draws, the probability of equal color is

    sum_(j!=i) p_j^2/(1-p_i)^2 <= s/(1-p_i)^2.

There are (K-1)^2 cross pairs of other draws. The finite union bound gives a conditional probability of any non-i match at most

    (K-1)^2 s/(1-p_i)^2 <= (1/16)/(7/8)^2 = 4/49 < 1/2.

Let F_ab be E_ab together with no such non-i match among these K left and K right draws. Therefore

    P(F_ab) >= (1/2) p_i^2(1-p_i)^(2K-2).

On F_ab the only color present on both sides of this block is i. Its two occurrences have both arrived by time 2K. Hence the chronological first match exists in this block and has color i, regardless of the relative locations a,b. In particular, the odd-time possibility R_b preceding L_a is included; no simultaneous-pair replacement or tie-breaking change occurs. The events F_ab remain disjoint.

Bernoulli's inequality for the nonnegative integer 2K-2 gives

    (1-p_i)^(2K-2) >= 1-(2K-2)p_i >= 1-2Kp_i >= 1/2.

Summing disjoint F_ab yields

    y_i >= (K^2/4) p_i^2 >= p_i^2/(256s) = x_i/256.

This proves y_i>=x_i/256 in all cases. For discrete probability laws the total variation identity is

    dTV(X,Y) = 1-sum_i min(x_i,y_i).

It follows directly by splitting each |x_i-y_i| into x_i+y_i-2min(x_i,y_i); all series converge absolutely. Since min(x_i,y_i)>=x_i/256, their sum is at least 1/256. Thus D(p,p)<=255/256, and consequently sup_p D(p,p)<=255/256<1. QED (ordinary proposal, independently unreviewed).

## Failed shortcuts and second route
The first-pair event alone proves y_i>=s x_i, but s tends to zero on diffuse laws; taking an infimum of s would lose strictness uniformly. Finite-dimensional compactness has the same uniformity problem when support size grows. Merely proving D(p,p)<1 separately for every p would not prove the requested strict supremum bound.

A second attempted route used independent Poisson processes for the first occurrence of each color on each side. It gives a useful competing-races intuition but independent left/right clocks do not preserve strict alternation. A proof only for that race would leave a model bridge. The finite K-block argument above eliminates the clock change and pays the actual chronological stopping rule directly. It also replaces an unproved negative-correlation claim with a conditional finite union bound; no numerical estimates, enumeration, CAS or probabilistic experiment was used.

## Novelty, prior and significance gates
Read actual final source Sections 9.1–9.2, including the proof of Theorem 3 and discussion separating Conjectures 4 and 5; read original Sections 2–4 for TV normalization. Figures 4–5 give numerical limiting-family evidence, not a premise of this proof. They were not visually inspected and no visual reading is claimed; no diagram is needed for the chronological block argument.

Exact allowlisted history and source-family reconciliation found no 1211.6486/shoe entry. This is bounded historical nonmatch, not worldwide novelty. Three native searches (9 exact query strings, all responses saved) found the original/final source but no identified subsequent full-bound theorem. Search absence proves nothing globally. Four current public registry root bodies and currentOid values were acquired; root HTML and indexed-search nonmatches do not clear uninspected repository proof bodies. Pinned upstream catalogue/tree searches found no exact shoe/Arratia/DeSalvo target title; broad sampling/discrepancy hits are not applicable theorems without a bridge. The pinned catalogue is older than current OpenAI head.

Specific public source bodies relied upon for the mathematics are actual guarded PDFs, not search excerpts. The current MathDB response contains the full apparent record plus a Cloudflare challenge-platform script at its end; conservatively treat that artifact as unavailable for clearance, do not retry or follow scripts. Its open/empty-solution presentation is not novelty evidence. No acceptance relies on it.

Strongest significance case FOR: this gives a dimension-free uniform constant for all discrete laws, directly answering the explicitly stated final-paper Conjecture 4. Neither the source's special limiting-family theorem nor the unequal-distribution construction proves it; the equal marginal condition is essential to the square-mass scale. Strongest case AGAINST: the argument uses elementary birthday-scale blocking and a union bound and may be known as a general collision-law minorization theorem. No applicable prior theorem with a complete target bridge has been identified/read here, so shortness alone does not justify a routine-adaptation exclusion. Independent significance/prior review must investigate precisely that possibility, including the broader collision-sampling literature and actual current registry proof bodies. We do not claim literature novelty or scientific qualification on bounded nonmatches.

Status: full ordinary derivation proposal; source model/final target paid for read passages; current proof-body registry/prior clearance incomplete; significance provisional; independent review absent; formal execution prohibited/not done; paper/replay/root acceptance absent; accepted=0, credit=0. No dispatch requested or made.
