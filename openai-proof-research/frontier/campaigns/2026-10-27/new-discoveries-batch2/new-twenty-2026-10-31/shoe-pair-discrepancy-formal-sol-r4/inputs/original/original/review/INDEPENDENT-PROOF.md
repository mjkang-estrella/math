# Independent ordinary proof for MathDB 324571

Review by GPT-6.1 Sol high/default, personally, without mathematical computation.
The following deductions were checked independently; FULLCANDIDATE.md is not a lemma.

Let p=(p_i) on N satisfy p_i>=0 and sum_i p_i=1. Finite laws extend by zeros; every discrete law can be relabeled on its countable positive support. On the countable product probability space take mutually independent L_a,R_b, all with law p. Reading coordinates in order L_1,R_1,L_2,R_2,... implements the source exactly. The countable product of discrete probability measures exists; each event used below depends on finitely many coordinates except the stopping variable, whose level sets are finite-coordinate measurable events. No Poisson embedding is used.

Write s=sum_i p_i^2. Since 0<=p_i<=1, s<=sum_i p_i=1. Some p_i is positive, so s>0; each p_i^2<=s, hence p_i<=sqrt(s). Independent pair equality has probability s by countable disjoint additivity. Conditioning one independent left/right pair on equality therefore gives x_i=p_i^2/s and sum_i x_i=1. Equivalently, repeated independent pair trials with memory reset have first-success color probability sum_{m>=1}(1-s)^(m-1)p_i^2=p_i^2/s, also when s=1.

Let T be the first chronological arrival after which a left/right color intersection is nonempty. Before T the intersection is empty. At T exactly one shoe is added; every new matching pair must use that shoe, so all new pairs have its single color. Thus the winning COLOR is unique, even if several opposite shoes of that color were already present. This establishes the source Y without an extra tie rule. On {T>2N}, necessarily L_j!=R_j for all j<=N. Those diagonal pair inequalities are independent, each with probability 1-s. Hence P(T>2N)<=(1-s)^N, which tends to zero. Continuity of probability for decreasing events proves P(T=infinity)=0. Define Y arbitrarily on that null event. Its measurable countable level sets partition almost surely, so y_i=P(Y=i)>=0 and sum_i y_i=1.

We prove y_i>=x_i/256 for every i. If s>=1/64, L_1=R_1=i forces T=2 and Y=i, so y_i>=p_i^2=s*x_i>=x_i/64>=x_i/256. This branch includes point masses (then both laws are the same point mass), s=1/64 and all p_i=1 possibilities.

Suppose 0<s<1/64. Set u=1/(4sqrt(s))>2 and K=floor(u). The elementary bounds K<=u and K>=u-1>=u/2 give
K>=1/(8sqrt(s)), K^2>=1/(64s), K^2*s<=1/16, and K>=2.
Fix i. If p_i=0 the claim is immediate. Otherwise 0<p_i<=sqrt(s)<1/8, so 1-p_i>7/8 and K*p_i<=1/4.

For a,b in {1,...,K}, let E_ab specify L_a=R_b=i and every other left coordinate among the first K, and every other right coordinate among the first K, differs from i. Independence gives P(E_ab)=p_i^2(1-p_i)^(2K-2)>0. These K^2 events are mutually disjoint: the unique location of i on each side determines a,b.

Here is the conditional-independence bridge explicitly. A product cylinder restricting the other 2K-2 coordinates to values j_c!=i has its joint probability with E_ab equal to p_i^2 times the product of their p_{j_c}. Dividing by P(E_ab) yields the product of p_{j_c}/(1-p_i). By countable additivity this also gives the conditional law of arbitrary coordinate subsets. Thus, conditional on E_ab, the other coordinates remain mutually independent with law q_j=p_j/(1-p_i) on j!=i, q_i=0. For each of the (K-1)^2 other left/right coordinate pairs, the conditional probability of equality is sum_{j!=i}p_j^2/(1-p_i)^2<=s/(1-p_i)^2. These pair-equality events need NOT be independent. The finite union bound alone shows their union B_ab has conditional probability at most
(K-1)^2*s/(1-p_i)^2 <= (1/16)/(7/8)^2 = 4/49 < 1/2.

Set F_ab=E_ab minus B_ab. Then P(F_ab)>=(1/2)p_i^2(1-p_i)^(2K-2). On F_ab the only common color in the two K-coordinate blocks is i. Both its occurrences have arrived by 2K. Their later chronological index is max(2a-1,2b), which is odd if a>b and even if a<=b. Before that time no color matches: a different matching color would be present on both sides of the block and would put the sample in B_ab; i itself has not yet appeared on both sides. Therefore T=max(2a-1,2b) and Y=i. There is no history outside the block before time 1; using future coordinates up to 2K merely defines a sufficient event, rather than conditioning the stopping process to continue. This pays the chronological bridge in both arrival orders.

For integer m>=0 and t in [0,1], (1-t)^m>=1-mt follows by induction: multiply the m inequality by 1-t>=0 and add the nonnegative mt^2 term. Applying it with m=2K-2 gives
(1-p_i)^(2K-2)>=1-(2K-2)p_i>=1-2Kp_i>=1/2.
Since the F_ab are disjoint subsets of {Y=i},
y_i>=sum_{a,b}P(F_ab)>=(K^2/4)p_i^2>=p_i^2/(256s)=x_i/256.
This is a finite sum over positions, not an independence assertion about different colors.

Finally sum_i|x_i-y_i| is finite since |x_i-y_i|<=x_i+y_i. Termwise |x_i-y_i|=x_i+y_i-2min(x_i,y_i), and countable summation gives (1/2)sum_i|x_i-y_i|=1-sum_i min(x_i,y_i). This equals the source's total variation convention: for A={i:x_i>=y_i}, the positive sum is attained, and every subset's signed sum lies between the total negative and positive sums, which are equal in magnitude because sum_i(x_i-y_i)=0. Since min(x_i,y_i)>=x_i/256, the overlap is at least 1/256. Consequently D(p,p)<=255/256 for EVERY discrete p. The same constant for every p gives sup_p D(p,p)<=255/256<1. This is stronger than separately showing D(p,p)<1. It proves the literal bound but makes no claim about the best constant or Conjecture 5.

Adversarial checks were deductive, not tests: zero coordinates never require conditioning on null E_ab; point masses never enter the divided-by-(1-p_i) branch; K=2 is allowed; the threshold equality is in the large branch; countably many colors enter only convergent nonnegative sums; same-side repeats are permitted; several opposite shoes of the winning color cannot create a color tie; an odd winning arrival is explicitly covered. No ordinary mathematical gap was found.
