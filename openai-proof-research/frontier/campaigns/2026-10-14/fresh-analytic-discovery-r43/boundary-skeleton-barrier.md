# Fixed jump blocks do not repair the source Lyapunov transfer

Author-side route analysis by Myeongjin Kang, no affiliation. Original prose CC BY 4.0. This is a technical obstruction to a proposed proof mechanism, not a new recurrence theorem and not a counterexample to stochastic recurrence.

## 1. Exact network and chain

Consider the reversible network

    0 <-> A,       2A <-> 3A+B,

with all four rate constants equal to one and falling-factorial stochastic mass action. At state (a,b) in Z_{≥0}^2 its four reaction intensities and increments are

| Reaction | Intensity | Increment |
|---|---:|---:|
| 0 -> A | 1 | (1,0) |
| A -> 0 | a | (-1,0) |
| 2A -> 3A+B | a(a-1) | (1,1) |
| 3A+B -> 2A | a(a-1)(a-2)b | (-1,-1) |

Factors with insufficient reactants mean intensity zero. Let Z_j denote the embedded discrete jump chain, started at Z_0=(N,0). Immigration guarantees strictly positive total jump rate everywhere. Fix an integer k>=1 BEFORE sending N to infinity. All constants O_k below may depend on k, never on N.

**Proposition.** Writing Z_k=(A_k,B_k),

    E[A_k-N] = 1-(k+1)/N+O_k(N^-2),                  k odd;
    E[A_k-N] = 2/N+O_k(N^-2),                        k even.

Consequently every fixed positive jump block has strictly positive A drift at all sufficiently large (N,0).

## 2. Full first-order path calculation

During the first k jumps, a=N+i with |i|<=k and 0<=b<=k. For N>k+3 all relevant factors are positive when their b condition permits them. The following expansions are uniform over this finite set of offsets.

At b=0, the total rate is

    1+a+a(a-1)=a^2+1.

Thus the (+1,+1) reaction has probability 1-N^-1+O_k(N^-2), the (-1,0) reaction has probability N^-1+O_k(N^-2), and immigration has probability O_k(N^-2).

At b>=1, the reverse (-1,-1) reaction has probability 1-(bN)^-1+O_k(N^-2), the forward (+1,+1) reaction has probability (bN)^-1+O_k(N^-2), and the sum of immigration and A-death probabilities is O_k(N^-2).

Call the first listed reaction in either case the baseline transition. Without a deviation, the chain alternates between offsets (0,0) and (1,1). A union bound over at most k transitions shows that paths with two or more deviations, or a transition already of order N^-2, contribute O_k(N^-2) to the expectation of the bounded displacement A_k-N. More formally, condition sequentially: at every reachable state the probability of a deviation is O_k(N^-1), so each specified pair of deviation times has probability O_k(N^-2). There are finitely many pairs and |A_k-N|<=k.

For a single deviation at time s, the pre-deviation state is a baseline state, so its first-order probability is exactly N^-1. The first-order coefficient in the expectation is the sum over s of the terminal A displacement after that deviation minus the baseline terminal displacement. This subtraction accounts for the probability lost from the no-deviation path.

* If s is odd, the deviation is A-death at a boundary state. Immediately afterwards the offset is (-1,0). Subsequent baseline transitions alternate (-1,0),(0,1). If k is even, the terminal A displacement is 0, equal to its baseline value. If k is odd, it is -1, instead of baseline 1. There are (k+1)/2 odd positions when k is odd, giving coefficient -(k+1).
* If s is even, the deviation is a forward reaction at offset (1,1), producing (2,2). The next two baseline transitions, when available, are (2,2)->(1,1)->(0,0). Thereafter the original baseline phase is restored. For odd k the terminal A displacement remains 1. For even k it remains 0 unless s=k, in which case it is 2. Thus the total coefficient is 2 for even k and zero for odd k.

These calculations prove the proposition, including k=1 and k=2. They do not let k grow with N.

## 3. Consequence for the actual pinned affine construction

Use the finite family F_h=min_λ(r_λ·z+b_λ(h)) from the October149 source, with its network tolerance and comparison directions for this exact network. Fix any positive reference point c; for sufficiently small h the source gives its constant ceiling M_h=F_h(c). Set h=1/N and z=(N,1)=X_h(-1,0). Then z is in the source box B_h.

For EVERY label active at z, the source coordinate sign-and-size condition forces r_B=0: if r_B were nonzero, it would force |p_B|>=H>0, whereas p_B=0. The activity tolerance is at most 1/2 and strict, so |r_A+1|<1/2, hence r_A<-1/2. These conclusions use precisely the all-active-label operation; no specially chosen branch is assumed.

Define the nonnegative convex deficit on integer states by

    V_h(a,b)=M_h-F_h(a,b+1).

For any active label r at z and ANY integer endpoint (a,b), the global supporting-affine inequality gives

    V_h(a,b)-V_h(N,0) >= -r_A(a-N)-r_B b = -r_A(a-N).

It is irrelevant whether the endpoint lies outside B_h, since F_h is a global finite affine minimum and only the initial activity test uses B_h. Therefore

    E[V_(1/N)(Z_k)]-V_(1/N)(N,0)
        >= -r_A E[A_k-N] > 0

for every fixed k and all sufficiently large N. This rules out a negative-drift argument using these source deficits and any fixed embedded-jump block, even at their own large-coordinate box boundary. It is a statement about this scale-indexed source operation. It does not assert that every possible fixed global Lyapunov function fails.

In particular, already at k=1 the continuous-time generator is positive: at (N,0), the stochastic mean drift is (N^2-2N+1, N(N-1)); multiplying the supporting inequality by the four rates gives

    L V_(1/N)(N,0) >= -r_A (N-1)^2 > 0  (N>1).

The deterministic reverse flux at the shifted positive point is present; the stochastic reverse flux at the actual state is exactly zero. Replacing those weights by positive monomials is the invalid step.

## 4. The standard entropy also fails every fixed jump block

Let v(a)=a log a-a+1, with 0 log0=0, and W(a,b)=v(a)+v(b). Uniformly over bounded offsets i,

    v(N+i)-v(N)=i log N+O_k(N^-1).

For odd k, the baseline endpoint has A displacement one and B=1. Thus

    E[W(Z_k)]-W(N,0)=log N+O_k(1)+O_k((log N)/N)>0.

For even k, the baseline endpoint is exactly (N,0). Any nonzero endpoint displacement requires a deviation, an event of probability O_k(N^-1). The Taylor remainder therefore has expectation O_k(N^-2), and the bounded B contribution is O_k(N^-1). By the proposition,

    E[W(Z_k)]-W(N,0)
      = (2 log N)/N + O_k(N^-1) + O_k((log N)/N^2)>0.

This is stronger than a one-step entropy failure: merely increasing a fixed block size does not cure it.

## 5. Why this is not a recurrence counterexample

The probability

    π(a,b)=exp(-2)/(a!b!)

satisfies detailed balance on each displayed reaction pair. For the nonlinear pair, the ratio of target to source probabilities is 1/[(a+1)(b+1)], and multiplying the target reverse rate (a+1)a(a-1)(b+1) yields the source forward rate a(a-1). The linear pair is equally direct. The total expected jump intensity under π is 4, since each relevant Poisson factorial moment is one.

For completeness, the usual minimal-chain path-reversal identity gives π(a,b)P_t((a,b),(c,d))=π(c,d)P_t((c,d),(a,b)), so πP_t<=π even before conservativity is known. Hence the compensator bound for jumps before explosion, started from π, is at most 4t. Infinite jumps in finite time consequently have probability zero. Since π gives every state positive mass, the same is true from every state. Conservation and πP_t<=π imply stationarity. All states communicate: immigrate enough A, use reverse nonlinear reactions to remove B one at a time, remove A to reach (0,0); reversing such paths is possible because the graph and each enabled move are reversible. An irreducible conservative countable chain with a stationary probability is positive recurrent.

This example is also deficiency zero (four complexes, two linkage classes, stoichiometric rank two). That observation is context, not a needed external theorem. The explicit stationary law provides a negative control against the incorrect conclusion that our drift failures disprove recurrence.

## 6. Comparison and exact remaining interface

Anderson–Cappelletti–Kim2020, Theorem6.1, assumes stochastic-top source complexes lie in the deterministic top tier along every proper tier sequence. At (N,0) the deterministic monomials (x∨1)^y have orders 1,N,N^2,N^3 for 0,A,2A,3A+B. The only deterministic top complex is 3A+B, but its stochastic propensity is zero. The stochastic top complex is 2A. Thus that hypothesis fails exactly, and the proof's bounded weighted-path estimates cannot be imported.

The pinned affine flattening does not fix this mismatch: its exact zero B slope makes the uncancelled terminal fast-phase displacement visible. The leading 2/N even-block term comes only from ending during a rare two-birth excursion; it is not a cumulative bulk outward drift. In contrast, every completed nonlinear excursion returning to B=0 preserves A, because the nonlinear reaction preserves A-B. This suggests sampling at state-dependent return times or adding a boundary Poisson corrector. Neither operation is supplied by the deterministic source. For arbitrary networks the fast boundary process can be infinite, have several linkage classes, and pass through additional species scales. Uniform integrability of such stopping times, a coercive corrected function, and drift estimates valid through all overlapping boundary regimes remain unproved here.

No restriction to this network, bounded molecularity, one linkage class, positive populations, finite classes, or a known complex-balanced subclass is substituted for the original provisional all-network question. No full stochastic scope was frozen. The outcome is a pre-freeze mechanism barrier, not a nominee.
