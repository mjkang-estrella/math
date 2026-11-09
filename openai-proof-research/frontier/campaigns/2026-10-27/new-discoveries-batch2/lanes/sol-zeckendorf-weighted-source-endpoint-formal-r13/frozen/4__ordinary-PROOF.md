# Ordinary mathematical endpoint: negative answer to Question 6.5 under P_N

Status: full ordinary proof, with an independently constructed single-type diamond partition. No Lean certificate, independent acceptance review, priority clearance or discovery credit is asserted.

## Literal theorem and dependencies

Use F_1=1,F_2=2,F_(i+1)=F_i+F_(i-1). For every integer N>=1 start from N copies of F_1. At each live configuration choose uniformly among its legal move types. The types are C_1:2F_1->F_2; C_k:F_(k-1)+F_k->F_(k+1), k>=2; S_2:2F_2->F_1+F_3; and S_k:2F_k->F_(k-2)+F_(k+1), k>=3. Indistinguishable choices of token instances are NOT separate types. Write P_N for this law. Let T be length, d_N its deterministic maximum, X_i=1 for an S move and zero for a C move, including C_1, and X_i=0 for i>T. Let alpha_N(k) be exactly Eq.(7), the supremum over cuts m and events in sigma(X_i:i<=m), sigma(X_i:i>=m+k).

Then, with n=n(N) defined by F_n<=N<F_(n+1),

    lim_(N->infinity) alpha_N(n(N)^6) = 1/4.

In particular for EVERY delta>0 and EVERY finite M>0, for ALL sufficiently large N,

    sum_(k>=0) (k+1)^2 alpha_N(k)^(delta/(4+delta)) > M.

This negates the full existence of delta,C uniform in N in Question 6.5, p.28, arXiv:2210.11038v1. It does not disprove Gaussianity of game lengths (Conjecture 1.7).

Source dependencies, read in the frozen actual PDF extraction: Definition1.2, Section1.2, Theorems1.1/1.3/1.6 (terminal form, combine count, d_N<3N). Source Lemmas4.1/4.2/4.4, read on pp.16–19, inspired the diamond method. To avoid importing their full combinatorial partition or notation, we prove the precise partition and abundance needed here from scratch using only C_2 <-> (S_2,C_1). Section5 component Gaussianity and Theorem1.10 residue equidistribution are NOT used. No interchange between P_N and mu_N is made.

## 1. Quantified local diamonds give unconditional anti-concentration

For each complete legal move word G, compress EVERY adjacent pair (S_2,C_1) to C_2; call the resulting word R. These pairs are disjoint (a letter cannot be both S_2 and C_1). Compression creates no new such adjacent pair: its replacement C_2 is neither letter of the pair. It also cannot destroy another pair. Compression is legal: the board before S_2 has h_2>=2, and the following C_1 is legal exactly when the original h_1>=1. The two-move change is (-1,-1,+1) in bins1,2,3, exactly C_2. Thus R is a legal complete game and contains no adjacent (S_2,C_1).

In R mark every C_2 for which the board BEFORE that move has h_2>=2. Its h_1>=1 already follows from legality of C_2. Such a slot may independently be left C_2 or expanded to S_2,C_1. Both choices return to the same board, so later legality and eligibility are unaffected. No new compressible pair occurs across a slot boundary: an expanded slot starts S_2 and ends C_1, while an unexpanded slot is C_2; an unmarked neighboring S_2,C_1 pair was already absent from R. Hence every expansion compresses back to R. Conversely, every word compressing to R is precisely one of these expansions: any removed pair leaves a marked legal C_2 at its position. This proves a disjoint exhaustive partition into Boolean cubes, with m(R) marked slots.

For the actual P_N law on each cube,

    T = length(R) + sum_(i=1)^m B_i,

where the B_i are conditionally independent Bernoulli(p_i). Here is the complete probability bridge. At slot i, the first short/expanded choice has the same factor1/b(s_i), while expansion requires one extra choice C_1 at the intermediate board, with factor1/b_i. The boards s_i and intermediate boards are fixed by R, unaffected by other slots, because the slot endpoints agree. Thus the weight of an expanded word is P_N(R) times the product of1/b_i over its expanded slots. Summing these weights gives the cube mass P_N(R) product_i(1+1/b_i); dividing gives the product law with p_i=1/(1+b_i). There are at most2n legal types, so 1/(2n+1)<=p_i<=1/2. The number of token instances does not enter these factors.

We next prove abundance of marked slots, rather than assume it. Fix c=3/2 and J=floor(N/6). At the start of each of the first J disjoint three-move blocks, bin1 has at least N-6(j-1)>=6 tokens, because each earlier move removes at most2 from that bin. These moves necessarily exist. The prescribed triple C_1,C_1,C_2 is therefore legal and has conditional probability at least p=(2n)^(-3). Its C_2 is a marked slot after compression: the two preceding C_1 moves create at least two F_2 tokens; the final C_2 is never compressed; the second C_1 is not removed in an S_2,C_1 pair because its predecessor is C_1. Earlier compression preserves the board before this C_2. Distinct successful blocks give distinct marked slots.

The block success indicators need not be independent. Their conditional success probabilities are >=p, so their sum stochastically dominates Bin(J,p). One direct construction uses an independent uniform per block to realize its conditional indicator with threshold q_j>=p, and compares with threshold p; the remaining block path can be sampled conditionally. With mu=Jp, Chernoff gives P(sum successes<mu/2)<=exp(-mu/8). Since N>=F_n and c<phi, mu/2>=c^n for all sufficiently large N, and mu->infinity. Consequently

    e_N=P_N(m(R(G))<c^n) <= exp(-mu/8) ->0.

This is an independently proved abundance bound for our single-type partition. It also explains how to repair the unnecessary independence wording for raw triple indicators in the primary Lemma4.4.

Put V=sum_i p_i(1-p_i). For n>=2, V>=m/(6n). For any integer-valued sum Y of these independent Bernoulli variables, Fourier inversion gives

    sup_a P(Y=a) <= (1/(2pi)) integral_(-pi)^pi |E exp(itY)| dt
                  <= sqrt(pi/(8V)).

Indeed |1-p+p exp(it)|^2=1-4p(1-p)sin^2(t/2); hence the product modulus is at most exp(-2V sin^2(t/2))<=exp(-2V t^2/pi^2) on [-pi,pi], using sin(|t|/2)>=|t|/pi. Extend this Gaussian integral to the real line to obtain the displayed constant. This proof also handles different p_i and does not use variance divergence as a substitute for anti-concentration.

Let e_N=P_N(m(R(G))<c^n)->0 by the abundance bound above. For ANY real interval I of length w>=0, with either endpoint convention, at most floor(w)+2 integers lie in I. Averaging conditional probabilities over the partition, regardless of the different cell centers, yields

    sup_(length(I)<=w) P_N(T in I)
       <= e_N + (floor(w)+2) sqrt(3*pi*n/(4c^n)).             (AC)

Thus Q_N=sup_(length(I)<=3n^6) P_N(T in I)->0. This is a proved law-of-total-probability bridge from the independently proved diamond partition to the actual P_N law. Mixtures can have different means/variances; that does not affect the concentration function estimate. No unconditional CLT is assumed or concluded.

## 2. A high-token hazard bounds the final combine-only suffix

Let H(s) be the total number of tokens at a board of value N. All occupied bins have index<=n. If H(s)>n+2, then with conditional probability at least

    p_n=(2n)^(-3)

a split occurs within the next three moves. Proof: if some bin of index>=2 already has at least two tokens, its split is legal immediately and is selected with probability >=1/(2n)>=p_n. Otherwise all n-1 such bins have height<=1 and h_1>=4. The prescribed path C_1,C_1,S_2 is legal, irrespective of their other contents. Each of its three type choices has probability >=1/(2n). This gives the bound without independence or a stationary-chain assumption. The path cannot terminate before that split.

Write L=max{i:X_i=1}, with L=0 if there is no split. For every integer q>=1,

    P_N(T-L > 3q+n+3) <= (d_N+1) (1-p_n)^q.              (SUF)

To see this without treating the last split as a stopping time, union over deterministic integers t=0,...,d_N. If t=L and T-t>3q+n+3, the next3q moves are combines and at each block start t+3j, 0<=j<q, more than n+2 tokens remain: the remaining combine-only moves each reduce H by one, ending at Z(N)>=1. Bound the probability of q consecutive no-split blocks whose block starts have H>n+2 by iterated conditional expectation and the hazard. If a block falls below that threshold it cannot belong to the event being bounded. Summing the per-t bound proves SUF. The union includes t=0 and so handles games with no splits.

Take q=n^5 and b_n=3n^5+n+3. By d_N<3N and N<F_(n+1)<=2^n (or the looser2^(n+1)),

    P_N(T-L>b_n) <= (3N+1) exp(-n^2/8) ->0.             (TAIL)

For all sufficiently large n, b_n<=n^6. This proves that the final combine-only suffix is small on the selected scale; it is not assumed deterministically short. In particular, combine-only paths of length order N are compatible with this estimate because their probability is small.

## 3. Deterministic median cuts give two robust branches

Let k_n=n^6. Choose the least integer m_N such that P_N(T<m_N)>=1/2. Minimality and (AC) give

    1/2 <= P_N(T<m_N) <= 1/2+Q_N,
    P_N(T>=m_N+2k_n) >= 1/2-2Q_N.

For the second inequality, the extra interval [m_N,m_N+2k_n) has length2k_n and mass<=Q_N. On the event T>=m_N+2k_n and T-L<=b_n<=k_n, L>=m_N+k_n. Consequently

    P_N(L>=m_N+k_n) >= 1/2-2Q_N-P_N(T-L>b_n) = 1/2-o(1).

Both tails are therefore >=1/3 for all sufficiently large N. These are actual probabilities under P_N, not selected path probabilities. The late-tail lower bound also ensures the cuts lie within the nontrivial source row for large N.

## 4. Observable stopping event and weighted obstruction

This step is the root-supplied mechanism frozen in ROUTE.md; the two preceding probabilistic estimates are this lane's contribution. Let C=N-Z(N), S_m=sum_(i<=m)X_i. Every combine, including C_1, decreases H by exactly one; every S preserves it. Hence every complete game has exactly C combines. If T<m, S_m=T-C and m-S_m=C+m-T>C. If T>=m, m-S_m is the actual number of combines in the first m moves and is <=C. Therefore

    {T<m}={m-S_m>C}.

This is a prefix-measurable event, including when T=m (neither strict inequality holds). It does not assert that the C-th combine terminates play. B={L>=m+k} is suffix-measurable, being the union of {X_i=1} for i>=m+k. A={T<m} and B are disjoint. Although Eq.(7) prints no absolute value, take A^c if necessary: covariance of A^c and B is +P(A)P(B). Thus

    alpha_N(k)>=P_N(T<m) P_N(L>=m+k).

At m=m_N,k=k_n the lower bound tends to1/4. For any events, absolute covariance is <=sqrt(P(A)(1-P(A))P(B)(1-P(B)))<=1/4, giving the claimed limit. For every0<=k<=k_n the same cut supplies the same eventual lower bound1/9. With r=delta/(4+delta)>0,

    sum_(k>=0)(k+1)^2 alpha_N(k)^r
       >= 9^(-r) (k_n+1)(k_n+2)(2k_n+3)/6 ->infinity.

This proves the literal negative endpoint with all delta,N quantifiers. It says nothing adverse about a separately normalized Gaussian limit for T.

## Dependency and objection audit

The scientific inputs about the stochastic partition are proved directly above. In particular, this proof does not depend on a cell-variance assertion, the source's full prefix tiling, or the component CLT. A harmless source indexing ambiguity is avoided explicitly: eligibility always refers to the board BEFORE C_2, since the move consumes one token from bin2; the displayed source h_k(i) condition uses notation elsewhere defined after move i. The physical move rule, not an after/before typo, fixes the diamond condition. All additional bridges are proved above: Fourier anti-concentration, averaging arbitrary centers, adaptive high-token hazard, deterministic-time union instead of conditioning at L, and quantile separation. A purported refutation of this proof must break one of those explicit assertions or an invoked established terminal-form/length theorem. No variance-only inference, uniform-complete-game substitution, or deterministic short-suffix premise remains.

This is elementary relative to the paper's diamonds and a standard stopping-event idea. A routine-adaptation objection is serious: the concentration estimate and hazard use standard methods. The precise potentially substantive result is the full uniform weighted mixing refutation, not any helper lemma or formalization. Root and an independent reviewer must adjudicate scientific credit and prior subsumption. No worldwide-priority assertion is made.
