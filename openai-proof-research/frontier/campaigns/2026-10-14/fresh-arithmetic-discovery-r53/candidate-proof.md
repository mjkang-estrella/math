# T024W52: every-endpoint short-interval asymptotic for distinct totients

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

**Author proof claim, pending independent proof and contribution assessment.** This continues the exact r52 question; it is not a new or weaker scope. No campaign acceptance, count increment or literature-priority claim is made.

## Theorem

Assume the stipulated source024 results at commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Let V(t) be the number of distinct positive values of Euler's totient function not exceeding t. Then, for the real variable x tending to infinity,

    V(x+x/log x)-V(x) ~ V(x)/log x.

There is no exceptional set of endpoints. The inherited frozen statement has SHA256066820343d15154d5ce3e737095287c1c90ba8c68c944acd3069b4ef6b84e012.

## 1. Dependencies and the local bridge

The source supplies the exact basic tuples, reciprocal mass M_1(Y;H), coarse-band/simplex geometry, global mass calibration, and the layered collision comparison. Its internal least-preimage companion does not assert the present all-window asymptotic. Classical Ford inputs supply only order bounds in short intervals and the stated sieve/normal-structure operations; they are credited in local-sieves.md.

Use Y=2x and h=x/log x. More generally the two local proof modules work uniformly for x in[Y/4,3Y/4], h comparable to Y/log Y and x+h<=Y. Fix a sufficiently large H first and form P=floor(log log H), R=m-H and L=m-P from Y. Keep these parameters fixed across the two endpoints.

The genuinely required local estimates are proved in local-sieves.md and local-coverage.md, rather than assumed from global error terms:

1. Local bad-prime counting uses a translated two-form sieve after the Ford bad-cofactor decomposition.
2. A split at p=sqrt Y converts the global bad-prime/preimage convolution into a local one. For small p it uses the pre-existing local upper bound for all totients; for large p it reverses the sum and uses the local bad-prime bound. This establishes S-niceness before any good-preimage hypothesis.
3. The first simplex failure is counted through a translated rough-number sieve. Later failures have a large available largest prime by the first simplex inequality and the Omega cutoff. Their reciprocal suffix estimates remain global, so only that prime count changes.
4. This localizes Ford16 and the fixed-eta part of Ford10 in the exact Psi<=sqrt(m) range needed here. The original geometry and coefficients are retained.
5. The resulting exceptional-value estimate is universal over preimages. The discarded-tuple estimate controls full failing witnesses, including the separate p_0-normality and i=0 square cases.

In particular, writing J=(x,x+h], the source tuple sets restricted to values in J have a coverage-exception set E_J and a discarded subset D_J satisfying

    |E_J|+|D_J| <= (epsilon_H+o_{Y;H}(1)) hG_m(Y)/log Y,
    epsilon_H ->0.                              (15)

Values with only bad preimages are included in E_J, as are values with both good and bad preimages. Outside E_J every preimage is basic. No selection of a convenient preimage has replaced this quantifier.

## 2. Ordered collisions in the same window

We give the local collision operation in full, including its interval-size requirement. In source layers.tex Proposition comparison, retain every hypothesis and additionally require the common product to lie in(a/r,b/r], with0<=a<b<=Y and delta=(b-a)/Y>=1/(C log Y). Its upper bound gains a factor delta, with only an absolute constant change depending on C.

Indeed, after fixing the source's lower configuration sigma_1 and t', write its top squarefree layer t_1#=t'Q and Z=Y/(r s_1# t'). The interval for Q has length delta Z and upper endpoint at most Z. Feasibility and the source's top-product/normality hypotheses imply

    Z>=Q>=Y^{1/(8 log_2 Y)}.

Hence log(delta Z)>=(1/2)log Z>=log Y/(16log_2 Y) for sufficiently large Y. Translate the Q interval. The prime forms become n+u,A(n+u)+1,A'(n+u)+1, where A!=A'; their determinant remains AA'(A-A'), of magnitude at most Y^3. Ford's uniform three-form sieve bounds the Q count by

    C delta Z (log_2 Y)^3 /log(delta Z)^3
      <= C' delta Z (log_2 Y)^6/(log Y)^3.

Primitivity and admissibility are translation invariant. If inadmissible there are at most three inputs, absorbed by the displayed bound; interval rounding is absorbed for the same reason. The source's reciprocal t' sum is unchanged. All later layer estimates are positive reciprocal sums uniform in the lower configuration, so the extra factor delta persists through the complete comparison argument. The full lower-layer proof was read; no sign cancellation or dependence on the location of the top interval is used there.

Apply this localized comparison to source collisions.tex at first unequal index i=0 with(a,b)=(x,x+h). Its strict-slack saving, tuple-recovery factors and all later sums stay unchanged, now with h in place of Y. For i>=1, p_0 is common to the two tuples. Fix the suffix pair and common intervening primes, retain feasible data until counting p_0, and use its actual value interval. The source's basic cofactor bound gives an endpoint Y^{1-o(1)} and the quantitative PNT supplies h/log Y times the same reciprocal cofactor. Then enlarge the positive reciprocal sums exactly as in the source. The resulting suffix-pair sum is the same convergent tail

    C sum_{k>=H} k^4 exp(-c rho^(-k)/k^3).

The first-index term has the source exp(-c B/m^4) saving, now relative to the local scale, so it tends to zero. We obtain the ordered-pair estimate

    K_J <= (epsilon_H+o_{Y;H}(1)) hG_m(Y)/log Y.  (16)

This counts ordered pairs of distinct good tuples with a common value in J, including the recovered tuple coordinates. It is not merely a count of collided values.

## 3. Tuples versus values

Let T_J be the finite set of distinct source tuples(p_0,...,p_R,d) admitting a basic witness and having value in J. Apply the source's finite-map counting lemma to its value map, with E_J,D_J,K_J from(15)-(16). Coverage holds outside E_J; every tuple represents an actual totient; the discarded tuples and ordered collision multiplicities have the required bounds. Thus

    ||T_J|-[V(x+h)-V(x)]|
       <= (epsilon_H+o_{Y;H}(1)) hG_m(Y)/log Y.  (17)

This use of the lemma is local from the outset. Subtracting two global cardinality formulas is not being used to obtain (17).

## 4. Prime sum and global calibration

For fixed remaining data(d,p_1,...,p_R) in the source D_H(Y), put

    D=d product_{i=1}^R(p_i-1).

The source bound is D<=exp((log Y)^0.8). The admissible largest primes for J are exactly

    1+x/D < p_0 <= 1+(x+h)/D.

Their lower endpoint exceeds Y^0.9 for large Y, so the basic lower cutoff is inactive. Every other basic condition depends only on the fixed data and u_0=log_2 Y. The quantitative PNT gives, uniformly in all these data,

    count = (1+o_Y(1)) h/(D log Y).

Here log(x/D)=log Y+O((log Y)^0.8); the endpoint PNT error divided by h/(D log Y) is O((log Y)^2 exp(-c sqrt(log Y))). Summing positive weights and using M_1(Y;H)<<K_H G_m(Y), with H fixed, yields

    |T_J| = h/log Y [ M_1(Y;H)+o_{Y;H}(G_m(Y)) ]. (18)

Combining(17)-(18),

    V(x+h)-V(x)
      = h/log Y [ M_1(Y;H)+(O(epsilon_H)+o_{Y;H}(1))G_m(Y) ].   (19)

Now use source Proposition mass with common ambient endpoint Y and fixed c=2. Since x=Y/2, it gives

    V(x)=x/log Y [M_1(Y;H)+(O(epsilon_H)+o_{Y;H}(1))G_m(Y)].    (20)

The same source proposition at Y, together with Ford's positive lower order bound V(Y)>>YG_m(Y)/log Y, shows M_1(Y;H)>=cG_m(Y) for all sufficiently large fixed H and then large Y. Thus the errors in(19)-(20) are small relative to their common positive mass. Divide the formulas, first let Y tend to infinity with H fixed, and then let H tend to infinity. This proves

    [V(x+h)-V(x)] / [(h/x)V(x)] ->1.

Since h/x=1/log x, the full frozen theorem follows. No continuity of the arithmetic phase factor, no variable-H rate and no interchange of iterated limits is required.

## 5. Contribution and scope limits

This is a complete author proof claim for the original target, not an independent gate. The source's distinct-prefix model and collision geometry remain fully credited. Ford's short-interval order theorem, normal-prime decomposition, simplex geometry and coefficient-uniform sieves remain classical inputs. The added interface is the uniform localization of exceptional values before a good representation is available, together with the compatible tuple/collision localizations. Whether that interface meets the campaign's substantial-contribution threshold is for independent assessment; no novelty or acceptance is inferred merely from completing the deduction.

The statement does not claim an effective rate, intervals x^theta, multiplicity-specific asymptotics, shrinking arithmetic-progression uniformity or a result on least-preimage ratios. These are limits of this theorem, not narrowed replacements of T024W52.
