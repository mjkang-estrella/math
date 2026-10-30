# r80: maximum-displacement unimodality — unresolved, credit 0

## Source and early screen

Selected source: Kyle Celano, Jennifer Elder, Kimberly P. Hadaway, Pamela E. Harris, Jeremy L. Martin, Amanda Priestley, Gabe Udell, arXiv:2507.07243v2 (19 September 2026), Conjecture 6.5. Actual latest HTML definitions, Theorem 2.10, Definition 3.2, Theorem 3.1, Section 4.1 including equations (6)–(10) and its proof, Section 5.2 equations (36)–(38), and Section 6 statements read. Saved source SHA256 dea598b34186ce650a8bf671d9f5daf183ef563fac0b68205bdd7db2be81e5a1. The abstract/history still lists v2 as latest. The author publication list calls this a preprint; no published version located or asserted. Read selected Section 4.1/4.2 and future-work bodies of the same-author companion 2508.11587v1; they study inversion enumeration, not maximum-displacement unimodality. This is a bounded comparison, not a full citing-literature audit.

For n cars with preferences in [n], cars arrive in order, each taking the first vacant spot at or after its preference. A parking function is one where all n cars park within [n]. Let a(n,l) count functions with largest individual displacement exactly l. The precise target is: for every integer n>=1, there exists c in {0,...,n-1} such that a(n,0),...,a(n,c) is weakly increasing and a(n,c),...,a(n,n-1) is weakly decreasing. This is not a total-displacement or sorted-preference question.

Four primary assertions were screened, with only the last receiving sustained work:

1. Leake–Mohammadi Yekta 2609.39917v1 Q1.7: general integer-mean fiber-count geometric-mean inequality. Actual statement read, then filename-first all-date duplicate gate identified r52, confirmed in r77. Excluded before mathematical investment.
2. Celano et al. Conjecture 5.5: fixed-inversion asymptotic bound. The source's own (36) gives, for each fixed k, upf(n,k)<=2^(n-1) binom(n+k-1,k)=O_k(2^(n-2k)n^k), merely by discarding code upper bounds and ascent weights. Thus fixed-k interpretation is routine. The screen does not resolve a uniform-in-k interpretation or exploit its wording. Existing first-campaign catalogue flags a reported solution, not audited here; no nomination.
3. Celano et al. Conjecture 6.3: Foata/spot commutation for unit-interval parking. The standardization mechanism below gives a short ordinary argument from source structure and preservation; recommend routine-corollary exclusion, no eligibility claim. Public actual Lean at Omega75fa71fb... explicitly says this conjecture is NOT proved and contains only distinct-letter/nondecreasing fragments. That body is not evidence of a full public resolution.
4. Celano et al. Conjecture 6.5: selected. Exact recurrence and generating function below; full unimodality remains unproved.

Duplicate searches cover ALL campaign-date trees, all .md/.json report names, including FINDINGS; they are not restricted to summaries or batch2. Saved filename list precedes bounded excerpt reads. Final capped rg uses --no-ignore --threads 1 --no-mmap, returns0 with empty stderr. Thirty initial matching files,55 bounded sections (including self-generated evidence) were recorded. Generic Mohammadian and historical entropy hits are unrelated. The first-campaign catalogue contains the neighboring inversion assertion, not evidence of a previous proof of6.5. Additional exact-ID/maximum-displacement filename searches returned catalogue and registry metadata hits; no prior campaign6.5 result established. No absolute freshness claim.

## Rigorous recurrence for the full source objects

Write C(n,l)=sum_{j=0}^l a(n,j), C(0,l)=1 for l>=0. For n>=1 and l>=0,

C(n,l)=sum_{k=1}^n binom(n-1,k-1) min(l+1,k) C(k-1,l) C(n-k,l). (R)

Proof: let the final car park in spot k. Before it arrives, every other spot is occupied. No earlier car ending to the right of k can have preferred a spot at or left of k, since it would stop at the still-vacant k; cars ending to the left cannot prefer a larger spot. Thus earlier cars split into two independent parking functions on the left and right intervals. Choose which k-1 of the first n-1 labels occupy the left, in binom(n-1,k-1) ways, then replace each subset's labels by their relative arrival order. Their displacement bounds remain l after translating the right interval. Conversely these data reconstruct the first n-1 preferences uniquely. The final car may prefer any of max(1,k-l),...,k, exactly min(l+1,k) choices. All other spots are full, so each such choice yields final displacement<=l. This is an inverse bijective decomposition and proves R for every n,l.

C(n,l)=C(n,n-1) for l>=n-1, and C(n,n-1)=(n+1)^(n-1), the classical full parking count. Define C(n,-1)=0 for n>=1. Then a(n,l)=C(n,l)-C(n,l-1). R is a helper, not a discovery nomination; it also follows by splitting the source's permutation-fiber formula at its maximum label.

## Exact generating-function route

All statements here are formal power-series identities over Q, avoiding analytic convergence assumptions. For fixed l>=0 set

F_l(z)=sum_{n>=0} C(n,l) z^n/n!,
P_l(z)=sum_{k=0}^{l-1} (l-k) (k+1)^(k-1) z^k/k!,

where the k=0 factor is defined as1 and an empty sum is0. Coefficientwise R yields

F_l'=(l+1)F_l^2-P_l F_l, F_l(0)=1. (E)

Indeed its first factor in the convolution is min(l+1,k+1)C(k,l). This equals (l+1)C(k,l) minus (l-k)C(k,l) when k<l. For k<l the bound is vacuous, so C(k,l)=(k+1)^(k-1), giving exactly P_l. The Cauchy product with factorial coefficients supplies binom(n,k).

Let E_l(z)=exp(-integral_0^z P_l(t)dt). Since E_l(0)=1, both it and the following denominator are formal units. Applying Y_l=1/F_l to E gives Y_l'=P_lY_l-(l+1), hence

F_l(z)= E_l(z)/(1-(l+1) integral_0^z E_l(t)dt). (Q)

This is exact for every l. For l0 it is 1/(1-z); for l1 it is 1/(2-exp z). For l2, E_l=exp(-2z-z^2/2). These cross-check the known permutation/Fubini enumerations.

The source requires the signs of

D(n,l)=a(n,l+1)-a(n,l)=C(n,l+1)-2C(n,l)+C(n,l-1)

as l ranges0,...,n-2 to have no negative-to-positive reversal. For l>=1, D(n,l)/n! is the coefficient of F_{l+1}-2F_l+F_{l-1}. For l0 and n>=1 use F_{-1}=1 to enforce C(n,-1)=0. Formula Q provides exact functions but does NOT prove their requisite coefficient sign ordering. A promising sharpened interface is to prove for each l that D(n,l) changes sign only from negative to positive with n, and that these transition sizes are ordered in l. Neither assertion is established by E or Q here.

## Failed stronger mechanisms and exact diagnostics

The recurrence was independently compared with literal parking of every preference word for n<=6 (46656 words at n6), and reproduces the source table through n9. Capped exact DP covers n<=500, all0<=l<n: no source-unimodality failure. This is finite evidence only.

A global log-concavity proof is impossible: at n80,l40, a(80,39)*a(80,41)>a(80,40)^2. Full integers and positive difference are in route-result.json, computed independently from R by route_checks.py. The first failure in the n<=140 screen is(80,40). This disproves a stronger helper, NOT Conjecture6.5; these entries do not form a valley.

Adjacent-size monotone likelihood ratios also fail: a(62,30)*a(61,31)>a(62,31)*a(61,30). Thus the intended inequality a(n,l+1)/a(n-1,l+1)>=a(n,l)/a(n-1,l) cannot provide a uniform total-positive induction. Its cross difference is saved exactly. Again this is not a source counterexample.

Nor can arbitrary positive mixtures of permutation fibers preserve unimodality. At n4, the identity car permutation's exact-max counts are(1,7,10,6), obtained by differencing product_{i=1}^4 min(l+1,i). The decreasing permutation has(1,0,0,0). Weighting the latter by20 gives(21,7,10,6), a strict valley. The source averages every permutation with weight1, so this artificial mixture is only a closure obstruction. A successful permutation-fiber proof must exploit the actual multiplicities and correlation structure.

234 factorial-scaled coefficients verify E for0<=l<=8 and0<=n<=25. These checks corroborate the displayed derivation, not the remaining sign theorem.

## Screen-only ordinary bridge for6.3, not nominated

Define stable standardization st(w) by ranking occurrences lexicographically by(value,original position). Source Theorem2.10 makes every unit-interval parking function a shuffle of its increasing blocks, with disjoint ordered value ranges; each block is (s,s,s+1,...,s+r-2) or singleton(s). Cars from other blocks do not affect its interval. In its prescribed internal order, its cars park in consecutive block spots. Therefore spot(w)=st(w).

Foata's recursive transform commutes with this stable standardization. To see this without an unproved slogan, label each occurrence by its stable rank in the full word. When appending a letter x, all earlier equal occurrences have smaller ranks. Thus comparison with the newly appended rank splits all earlier occurrences into exactly the same two groups as the comparisons <=x and >x. Foata's step partitions into blocks consisting of a run of one comparison class followed by one letter of the other class, and rotates the last letter to the front. Such rotations do not change the relative order of occurrences of ANY fixed value: the moved letter crosses only letters in the opposite comparison class, hence different values. By induction, earlier equal occurrences stay in their original order, the partitions/rotations of ranks and letters match at every recursive step, and the output labels are precisely the stable standardization labels of the output word. Consequently st(F(w))=F(st(w)) for every word.

Source Theorem3.1 ensures F(w) is again unit interval. Apply the preceding two identities to get spot(F(w))=st(F(w))=F(st(w))=F(spot(w)). Exact checks on3280 words over alphabet{1,2,3} through length7 corroborate the generic identity, but the ordinary proof is the argument above. This short structural composition has a serious routine-corollary objection; it is screened out rather than advanced as a substantive candidate. No paper/Lean investment.

## Freshness and limits

Read-only supplied COMPLETE inventories: Omega70af54071bfd4ac098619a9db8c16bb6f7aced11,350009 paths; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a,174524 paths, both dated17:20UTC. They are not called current. Targeted inventory paths identify UnitIntervalParkingFoata; actual full relevant Lean body was fetched at the newer75fa71fb84c19580a0ea89b3dc7c8158f7aa7446 and read, not just its Blueprint/badges. It leaves6.3 unproved and does not establish6.5.

The ordinary public Omega repository page fetched at18:04:56UTC now gives HEAD11c6ddfe2cea3073341c23f38a9fab84fd53266e, newer even than r78's75fa71fb. No complete new tree/delta audit obtained. Current registry freshness remains HOLD for all novelty claims. Public search found source/author/companion items, not an exact6.5 solution; absence from that bounded search proves nothing. No browser, account, git, contact, posting, upload, shared-write or other-lane-write actions.

Strongest mathematical falsifier: a genuine negative-to-positive reversal among the D(n,l) for some n>500, certified using R or direct source counts. Strongest objection to the attempted proof is that its proposed stronger log-concavity and likelihood-ratio invariants are actually false. Remaining FULL-SCOPE GAP: no all-n single-crossing theorem for the coefficient differences of Q, and no source counterexample. No PROOF.md, formalization, manuscript, acceptance, or count change. Worker credit0; total remains37/additional7.
