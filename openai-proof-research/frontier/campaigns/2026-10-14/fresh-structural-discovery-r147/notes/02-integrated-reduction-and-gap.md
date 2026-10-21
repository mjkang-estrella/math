# Strongest integrated route; PREFREEZE / no nominee

The original I128 Section2.B stationary Markov-deletion scope is retained in full, including kappa-uniform constants, arbitrary binary input, stationary initial law, rational encoding, exp(C_kappa(log n)^3(1+log log n)^6) traces, and every-stream polynomial work in that budget. No viable full theorem emerged and no frozen statement was created. I152's independent heterogeneous-retention target and its post-deletion noise deductions are separate unchanged antecedents. The calculations below are not correctness/contribution grades or substitute nominees.

## Source operations that already compose

The complete uniform Source122 proof was read, including the Gram-chain multiscale step, Gaussian contour conversion, spanning-tree allocation of gap costs, simultaneous Cayley-strip continuation, and capped rational decoder. Its initial source-coordinate discrepancy and the entire multiscale construction depend on Boolean moment positivity and prefix agreement, not the deletion channel. Those operations remain available for the Markov problem.

The channel-dependent step is equation `trace-generating-identity` in separation.tex: one scalar factor q+pu per source gap identifies the observable generating function with the input tuple polynomial. Its continuation proof then uses an actual bound on that SAME polynomial on a product of deletion disks. For a Markov channel, note01 gives an exact replacement as a product of scalar two-mode gap kernels. The count of source positions and hidden states is fully finite, and the selected retained endpoints reset the state. Thus matrix dimension alone is not the problem.

The complete decoder proof requires only: nonnegative rank-statistic coefficients with total mass<=1; efficiently constructible rational coefficients; separation from every wrong-prefix positive moment array; and ordinary independent trace repetitions. All but separation have been supplied here by the two-state dynamic program and the source's existing slack mixture and rational feasibility proof. The bit length is polynomial in n and the input encoding, and n^O(D) tuple enumeration is compatible with the old budget for D=O_kappa((log n)^2), as in the source. No new generic semidefinite algorithm is needed.

There is also a compatible small-perturbation calculation, not a replacement scope. Write P=Pi+c(I-Pi), where every row of Pi is the stationary law and c=1-a-b. Couple the stationary Markov mask and iid mask with the same first state. Conditional on agreement so far, a step fails to couple with probability at most |c|, so their mask-law TV distance is at most(n-1)|c|. For a fixed rank set I, aggregating mask probabilities by the source tuple gives coefficient l1 difference at most twice that TV. A positive moment functional has |E X_J|<=1, while evaluation at a Boolean word changes by at most TV for the bounded rank observable. Consequently the separation discrepancy changes by at most3(n-1)|c|. The iid separation therefore survives when this is at most half its source gap. This properly credits coupling plus the full decoder; it only reaches an inverse-quasipolynomial neighborhood of independence and does not establish I128's whole fixed-kappa class.

## An exact renewal attempt and its limit

The retained source positions form a delayed renewal process. After any retained position the iid gap PGF is

    g(s)=s(B-cs)/(1-As),  A=1-a, B=1-b, c=1-a-b.

This is a stronger simplification than generic exponential mixing. A thinning of observed output ranks with iid positive integer gaps N, independent of symbols, would compose g with the PGF h of N. To produce Bernoulli retentions r at source positions, its interior gaps must obey h(g(s))=rs/(1-(1-r)s).

Power-series coefficients uniquely force

    h1=r/B,
    h2=r((1-r)B-ab)/B^3.

This follows by comparing coefficients of s and s^2: g1=B and g2=ab. For the allowed chain a=b=4/5 (kappa=1/5), B=1/5 and ab=16/25>B. Thus h2<0 for EVERY r in(0,1]; no probability generating function h exists. In the exact diagnostic r=1/10 gives h1=1/2 and h2=-23/4. This excludes independent renewal output-rank thinning, not just Bernoulli thinning. It does not exclude symbol-dependent transformations, length-conditioned global kernels, extra statistics, approximate experiment comparisons, or source/classical constructions of a different type. Positive-correlated chains are not declared impossible either. The first-wait distribution and finite-stream sampling would remain additional obligations even in a case where the interior PGF has nonnegative coefficients.

## Why a generic analytic inverse is not the full transfer

The actual Cheraghchi–Downs–Ribeiro–Veliche primary, arXiv:2102.09490v1, Section1.3 and Lemma4, assumes independent random output blocks at EACH INPUT SYMBOL. Its mean identity is a single PGF substitution, and Lemmas6–7 give a local inverse near1. The full proofs of those operations and the tail estimate were read. A Markov mask is independent over retained-position gaps, not over input symbols, so that theorem cannot be imported by replacing its PGF name. Conversely local inversion itself is entirely compatible: the eigenvalue branch of P D(u) through1 has derivative pi1>0. No claimed obstruction is based on failure of the local inverse-function theorem.

For the within-gap kernel let H(t,u)=sum_(m>=0) B_m(u)t^m. Direct inversion of the two-by-two matrix gives

    H(t,u)=(B-ct)/[1-(A+Bu)t+cut^2]
          =h0(t)/(1-u g(t)),
    h0(t)=(B-ct)/(1-At)=g(t)/t.

The stationary prefix kernel has generating function

    sum A_m(u)t^m=pi1(1-ct)/[1-(A+Bu)t+cut^2].

These rational identities keep the initial boundary distinct from interior gaps. Their iid specialization c=0 agrees with the source.

Consider the particularly direct scalar inverse filter: choose rank weights w_j so that applying the functional u^j -> w_j sends B_m(u) to lambda^m for EVERY m. Triangularity makes these weights unique because the leading coefficient of B_m is B^(m+1)>0. If W(z)=sum w_j z^j and t=g^(-1)(z) is the branch through0, the identity above forces

    W(z)=1/[h0(t)(1-lambda t)]=t/[z(1-lambda t)].      (F)

For a=b=4/5 the inverse branch satisfies

    c t^2-(B+Az)t+z=0,
    discriminant=(z^2+62z+1)/25.

Its nearest negative branch point is z0=-31+8sqrt(15), with radius R=31-8sqrt(15) between1/63 and1/61. At that point t0=-(1+z0)/6 is finite and negative. For lambda=1, the map t -> t/(1-t) has nonzero derivative there and no pole; division by z0 is harmless. Thus the square-root branch persists in W. Its Taylor radius is at most R, so Cauchy–Hadamard gives limsup |w_j|^(1/j)>=1/R>61. This is exponential growth along a subsequence for THIS exact filter. The exact first weights are5,-55,1805,-70255,3056405. It is not a floating-point conditioning claim.

The target lambda=1 here is a boundary diagnostic, not a purported source witness. A raw exact all-gap filter therefore has no uniformly bounded rank-weight norm; finite truncations do not by themselves give the required inverse-quasipolynomial error. This does not prove a lower bound on trace reconstruction, on all mean algorithms, or on approximate filters on the special source-produced family of discrepancies.

## Long-gap approximation and the unpaid short-gap part

Near u=1, the two simple eigenvalues of K(u) are1 and c at u=1. For entries in[kappa,1-kappa], |c|<=1-2kappa. On a sufficiently small common complex neighborhood, depending on kappa, analytic spectral projections are uniformly bounded and the second eigenvalue has modulus at most rho_kappa<1. Restrict to the part of that neighborhood where the principal eigenvalue also has modulus<=1; such points include a real interval ending at1. Each A_m or B_m can then be replaced by its principal-mode part with absolute error <=C_kappa rho_kappa^m. The kernel and both spectral parts are bounded by C_kappa there. These facts follow directly from the quadratic roots and compactness of the permitted real parameter square; they do not use an unproved global spectral chart.

For an order-k tuple whose prefix and every open gap have length at least L0, telescoping the product gives error at most k C_kappa^k rho_kappa^L0. Summing over at most n^k tuples and using |Delta X_J|<=2 bounds the discrepancy error by

    2 n^k k C_kappa^k rho_kappa^L0.                  (E)

Thus choosing L0=O_kappa(log(1/epsilon)+k log n+k) pays this error at any desired epsilon, including the old inverse-quasipolynomial scale. This is a compatible useful estimate; it is incorrect to leave all Markov dependence unpaid merely because masks are correlated.

There are two remaining compatibility issues. First, Source122's final input witness is not guaranteed to lie in this small principal-eigenvalue chart. Its one-strip continuation would need a replacement domain on which the observable sum controls the needed input function, rather than only a locally isolated mode. Second, the source tuple polynomial includes arbitrarily short prefix/gaps, including adjacency. Removing those tuples can remove its entire detected discrepancy. At u=1, for example,

    B_m(1)=pi1+(1-pi1)c^(m+1).

The second mode has negative coefficient for c<0, and at m=0 in the example it cancels3/5 of the principal term. It cannot be treated as a uniformly tiny perturbation.

Partitioning source tuples by which gaps are<L0 and by their exact lengths costs at most(L0+1)^k categories. This combinatorial enumeration itself is affordable. But a category is defined using UNOBSERVED INPUT GAPS. It is not a supplied event on a trace. The triangular scalar filter above illustrates why coefficient computability is different from a stable observable realization of such categories.

One can expand a short cluster into contiguous source positions, using wildcard predicates at intermediate positions, as in the latest-anchor companion's exact-gap bookkeeping. This does not change the monomial's Boolean degree when a predicate is the constant1, but it DOES change the tuple's retained-slot order, which pays retention factors and rank enumeration in that proof. The naive expansion uses up to O(k L0) slots. At k of order(log n)^2 and log(1/epsilon) of order(log n)^3(1+log log n)^6, those costs need not fit I128's original exponent. Moreover this source bookkeeping still uses iid binomial gap transfer; merely inserting wildcards does not prove its Markov analog. No weaker-budget theorem is substituted.

The full BVW primary deconvolution Lemmas28–32, Corollary33, and Proposition36 proof were examined: they do control smooth Fourier cutoffs, support enlargement, and inverse norms, rather than attempting an unrestricted inverse. Those operations must be credited as a potentially compatible alternative. Their actual proofs divide a binomial characteristic function and use independent-prefix convolution and one-trace simulation of several independent iid deletion traces. We have not proved the Markov versions with the necessary prefix conditioning, degree and norm budgets.

To see one precise simulation issue, the union of two independent Markov masks is the OR of a four-state chain. From hidden label01 its next-step probability of union-deletion is (1-a)b; from label11 it is b^2, different in general (4/25 versus16/25 in the example). Hence conditional label probabilities depend on hidden gap lengths. BVW Lemma17's iid per-position labeling of an observed union trace is not justified by the mere existence of a finite-state union chain. This example does not rule out a more elaborate conditional simulation. The source's channel-independent Gram route already avoids needing that simulation up to its final transfer.

## Exact unresolved obligation

The strongest integrated route retains the full source-coordinate Gram/contour machinery; the exact Markov tuple kernels and rational coefficient algorithm; the local spectral inverse and long-gap estimate(E); and the source's statistical estimation, strict prefix slack and capped rational decoder. It also retains primary smooth deconvolution and renewal/channel-composition ideas at their actual interfaces.

What has NOT been supplied is a stable observable transfer for the ORIGINAL full tuple discrepancy, including all short gaps and the stationary prefix, uniform in every wrong-prefix positive Boolean moment functional and every P in the original kappa class. One sufficient missing statement would produce degree D=O_kappa((log n)^2) rank statistics with separation at least exp(-C_kappa(log n)^3(1+log log n)^6). Another mechanism could prove the original decoder theorem directly. We have neither. Exact kernels, local eigenvalue inversion, small-perturbation coupling and exponentially decaying long-gap errors do not establish that uniform statement.

There is no frozen theorem, full author proof, impossibility result, exhaustive-search claim, priority claim or current-open claim. The retained calculations are research support and precise route diagnostics; no importance, difficulty, hypothesis removal or completion of an old quantifier is offered as substantial-contribution evidence.
