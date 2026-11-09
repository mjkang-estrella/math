.po 0.8i
.ll 6.9i
.nr PS 10
.nr VS 13
.TL
A uniform discrepancy bound for alternating shoes
MathDB 324571 - implementation report, credit zero
.NH 1
Statement and checked model
.PP
Let p be any probability mass function on the natural-number colors, including infinite support. Draw independent coordinates in the strict order L1,R1,L2,R2,..., all with law p. Method X selects the color of an independent left/right pair conditional on equality. Method Y selects the color of the newly arriving shoe at the first chronological left/right match. Same-side repetitions do not stop the process. Define Y arbitrarily on nontermination.
.PP
The checked theorem Shoe.source_strict_universal_supremum states, for every natural-number fallback color c, that the supremum over ALL PMF Nat of the source discrepancies is at most 255/256 and is strictly less than one. Source discrepancy is the supremum, over arbitrary subsets A of Nat, of the absolute difference of the two probability measures of A. It is not a theorem merely bounding each discrepancy separately by an unspecified number less than one.
.PP
The source is Arratia and DeSalvo, On the Random Sampling of Pairs, with Pedestrian Examples, Advances in Applied Probability 47 (2015), 292-305, DOI 10.1239/aap/1427814592. Final Section 9.1 fixes strict left/right alternation and explicitly warns that simultaneous-pair tie rules differ. Final Section 9.2, Conjecture 4, equation (19), asks for the strict supremum. Original arXiv 1211.6486v2 has the corresponding Conjecture 4, equation (30). This report does not claim the optimal constant or resolve Conjecture 5.
.PP
The earlier modules supply the genuine infinite iid product measure, arbitrary finite-cylinder probabilities, measurable least chronological matching prefix, unique winning color, conditional pair law, and almost-sure termination. Time coordinate 0 is L1, coordinate 1 is R1, and coordinate 2 is L2. The HasMatch predicate requires one even and one odd coordinate strictly below the prefix length.
.PP
Put s=sum_i p_i^2. The normalized conditional law has mass x_i=p_i^2/s. Positivity and s<=1 are proved, including ENNReal finiteness and conversion to real numbers. Each p_i^2<=s, so p_i<=sqrt(s). Nontermination has probability zero: absence of any match through 2N implies failure of the N independent aligned pairs, of probability (1-s)^N, tending to zero. The final sourceY_eq theorem explicitly uses this almost-sure termination to remove all dependence on the fallback.
.NH 1
Scale and isolated events
.PP
For s>=1/64, the first-pair event L1=R1=i forces the actual winner to have color i. Thus y_i>=p_i^2=s*x_i>=x_i/64>=x_i/256. This branch covers point masses, threshold equality, and p_i=1.
.PP
For 0<s<1/64, set K=floor(1/(4 sqrt(s))). Direct floor inequalities give K>=2, K>=1/(8 sqrt(s)), K^2*s<=1/16, and K*p_i<=1/4. These statements are proved in ShoeScale, rather than supplied as assumptions on a block.
.PP
For 0<=a,b<K, E_ab requires that exactly left position a and right position b have color i among the first K positions on each side. Its equality to an actual finite cylinder is proved coordinate by coordinate. The iid cylinder theorem and two erased positions in the finite product give exactly
.PP
P(E_ab)=p_i^2*(1-p_i)^(2K-2).
.PP
Bernoulli's inequality (1-t)^n>=1-n*t follows by induction for 0<=t<=1. Since (2K-2)*p_i<=2K*p_i<=1/2, it yields P(E_ab)>=p_i^2/2. Neither this probability nor the required independence is encoded in a structure or assumed hypothesis.
.NH 1
Unconditional collision estimate and winning-law minorization
.PP
The implementation uses a simpler unconditional equivalent of the supplied conditional argument. For c!=a and d!=b, E_ab together with L_c=R_d is contained in the countable union, over colors j, of the four-coordinate events
.PP
L_a=i, R_b=i, L_c=j, R_d=j.
.PP
These four coordinates are distinct. Their exact probability is p_i^2*p_j^2, by the genuine finite-cylinder product law. Countable subadditivity therefore bounds the competing-pair event by p_i^2*s. Dropping the other restrictions of E_ab here only enlarges the event. In particular, no independence of overlapping competing-pair events is claimed.
.PP
Let F_ab be E_ab with every other left/right collision excluded. The finite union bound, even enlarged to K^2 potential competing pairs, gives
.PP
P(E_ab)<=P(F_ab)+K^2*p_i^2*s.
.PP
As K^2*s<=1/16 and P(E_ab)>=p_i^2/2, we obtain P(F_ab)>=7*p_i^2/16>=p_i^2/4. This unconditional estimate avoids division by (1-p_i), and works without conditioning on a positive-probability E_ab. Zero coordinates are covered directly.
.PP
On F_ab the only color common to the two K-blocks is i. Both occurrences arrive by 2K, so the actual least chronological match has color i, whether the left or the right occurrence arrives last. This consumes the existing winner_of_goodBlock theorem. Distinct position pairs give disjoint F_ab, by isolated_positions_unique. Measurability of every GoodBlock event is proved, and finite disjoint additivity places the sum of their probabilities below the actual winningLaw mass.
.PP
There are K^2 position pairs. Consequently
.PP
y_i >= K^2*p_i^2/4 >= p_i^2/(256*s) = x_i/256.
.PP
Shoe.winningLaw_minorization combines this argument with the large-s first-pair branch for every PMF Nat and every color. It assumes neither minorization nor a uniform bound.
.NH 1
Countable total variation and the uniform supremum
.PP
Both mass sequences have absolutely convergent sums equal to one. The minimum sequence is nonnegative and dominated by x; the absolute difference sequence is dominated by x+y, hence summable. Summing the termwise identity
.PP
|x_i-y_i|=x_i+y_i-2*min(x_i,y_i)
.PP
gives TV=1-sum_i min(x_i,y_i). Pointwise minorization implies min(x_i,y_i)>=x_i/256. Summation gives TV<=255/256 uniformly.
.PP
For completeness, the implementation also proves equality with the source supremum-over-subsets definition. The positive difference sequence max(x_i-y_i,0) is summable and has sum TV because sum_i(x_i-y_i)=0. Every subset's signed mass difference is bounded above by that sum; reversing the laws gives the opposite inequality. The set of colors with x_i>=y_i attains the bound. The PMF-to-measure indicator-series identity is proved for every subset of Nat. Thus sourceTV equals half the countable l1 distance, not merely a new convention chosen for this implementation.
.PP
Finally the same numerical bound holds for every law. Taking the supremum preserves the bound 255/256<1. The endpoint uses conditionalColorMeasure_toPMF and sourceY_eq, so normalized independent-pair sampling and almost-sure fallback invariance participate in its chain.
.NH 1
Validation, source map, and retained gates
.PP
Pinned Lean is 4.34.1, binary SHA256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550; mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. Binaries and on-disk pin metadata were verified under the immutable runner. Production proofs use no sorry, admit, added axioms, unsafe, or native_decide. Strict checks use -j1 -M3500 -DwarningAsError=true; independent leanchecker runs follow each successful production build.
.PP
Source map: conditional pair sampling -> ShoePair/ShoeConditional/sourceX; strict chronological Y -> ShoeBase/ShoeStopping/ShoeBlock/sourceY; iid cylinders -> ShoeProbability/ShoeBlockProbability/ShoeCollision; termination -> ShoeDiagonal/ShoeTermination/sourceY_eq; scale -> ShoeScale; probability minorization -> ShoeBlockSum/ShoeMinorization; source Section 4 TV -> ShoeTV/ShoeSourceTV; Conjecture 4 equation (19) -> ShoeEndpoint.source_strict_universal_supremum.
.PP
The fresh replay starts with an empty build and copies source text only. Its search path replaces the working build with replay/build and otherwise uses pinned upstream dependencies. No legacy olean is imported. Compiler/checker receipts, source equality, and post-checker olean hashes are inventoried separately. Historical failing diagnostic probes and the failed deep audit are not production-pass modules.
.PP
Positive controls cover a constant sample, odd chronological arrival, permitted same-side repeats, fallback independence, and universal-law specialization. The clean intentional same-side mutation fails only at its false equality goal. The inherited negative-control failure with a secondary subproof failure remains historical and is not recounted as a clean control.
.PP
UNPAID: the requested general arbitrary-countable relabeling and finite-zero-extension invariance certificates are not implemented beyond the source's explicit Nat model, which already permits zeros and infinite support. Whole-environment/private/generated/transitive body-origin DAG audit failed three capped attempts with Lean interpreter memory exceptions (exit -6); no successful full DAG or per-endpoint body closure is claimed. Named endpoint axiom reports are a narrower check and do not pay that gate. Independent final source-to-Lean/proof/deep-body/manuscript review and root acceptance are separate and unpaid.
.PP
The supplied bounded prior-art review is retained with its limits. Galbraith-Holmes (2012), A non-uniform birthday problem with applications to discrete logarithms, remains body-404/unread and unavailable; no alternate delivery was attempted. No worldwide priority or novelty claim follows from bounded search nonmatches. All inherited access denials remain binding. No new network retrieval, child agent, git operation, installation, account action, publication, shared-ledger write, or credit was performed here.
.PP
Process deviations are preserved: initial receipt/log display occurred outside the capped runner; early mandatory dumps were materially truncated and relevant mathematical passages recovered; a checker was invoked after a failed ShoeBlockSum compile and failed honestly; an audit shell-session identifier was not displayed, so no next compiler job started until its fixed cap had elapsed; orchestration-only JavaScript errors issued no shell command. Resource records are sampled per-group, not cgroup guarantees. All completed runner receipts retain true exits and report no remaining group members.
.PP
Disposition: checked source-Nat uniform theorem and source-only replay, with explicit outstanding gates. NOT TECHNICAL PASS, NOT ACCEPTED. Credit 0; campaign 55/60 beyond 39 prior, unchanged.

