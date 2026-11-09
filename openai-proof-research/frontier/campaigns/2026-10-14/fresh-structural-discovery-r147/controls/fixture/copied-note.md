# PREFREEZE: finite-state deletion masks

One selected family: Source122 trace reconstruction, with its uniform decoder, latest-anchor companion, and lower-bound companion as dependencies/comparisons within the family. No theorem is frozen. This is not a renamed H152 nomination: H152 retains arbitrary known position-dependent independent retentions in its original interval. Here the exploratory model is a stationary two-state Markov mask, constant transition matrix across source positions, independent repetitions across traces. This model is distinct, but distinction alone is not substantial evidence.

Write P=[[1-a,a],[b,1-b]], with 0<a,b<1, rational known parameters; state1 retains the input bit and state0 deletes it. Initial state before position1 has stationary distribution pi=(b,a)/(a+b). Set A=1-a, B=1-b, c=1-a-b. The input word has known length n; input positions and mask states are unobserved. No uniform quantitative theorem over varying a,b has been selected; in feasibility calculations the parameters may be fixed away from endpoints.

## Exact low-order channel coefficients

Put D(u)=diag(1,u), e=(0,1)^T, K(u)=P D(u). For m>=0 define

    A_m(u)=pi K(u)^m P e,    B_m(u)=e^T K(u)^m P e.

For selected positions i1<...<ik, the generating weight for their appearing as selected trace ranks is

    A_(i1-1)(u0) product_(r=1,...,k-1) B_(i(r+1)-ir-1)(ur).

Every selected input position is forced retained; every intervening unselected position is weighted by u if retained and by1 if deleted. Conditioning on each selected retained state resets the chain at state1, explaining the product over gaps. The tail after ik sums to1. For a rank tuple l1<...<lk, extract coefficient u0^(l1-1) product ur^(l(r+1)-lr-1). This gives the exact nonnegative coefficient of X_i1...X_ik in the rank statistic T_I. Summing over source tuples yields total coefficient at most1, since the originating tuples are disjoint events.

Dynamic programming on two states and retained-count coordinates computes the coefficients in polynomial time per pair of rank/input tuples. Rational transition products have O(nL) bits if L is the parameter encoding length; addition costs only polynomial extra bits because denominators share a product of the fixed input denominators. Enumeration for degree D costs n^O(D), rather than enumerating all 2^n masks.

Source122's Boolean positive moment matrix, correct-prefix strict slack, concentration, bounded rational feasibility iterations and all-stream halting proof therefore remain compatible PROVIDED a degree-D wrong-prefix separation bound is supplied. These are credited operative source operations; replacing binomial coefficients by a two-state dynamic program is not a substantial result.

## Renewal reduction, stronger than merely replacing independence by mixing

After a retained position the distance G to the next retained position is independent of earlier such distances. Its law and generating function are

    Pr(G=1)=B; Pr(G=j)=ab A^(j-2), j>=2;
    g(s)=B s+ab s^2/(1-A s)=s(B-c s)/(1-A s).

If a trace-only thinning keeps a renewal subsequence of output ranks with positive integer iid gaps N independent of the observed symbols, then the retained source gap has PGF h(g(s)), where h is the PGF of N. To obtain iid source retentions r, a necessary interior-gap identity is

    h(g(s))=r s/(1-(1-r)s).                         (R)

The first selected position also needs the correct geometric law; satisfying interior gaps alone is insufficient for an ordinary deletion channel on a finite word. The stationary first-wait law is different from G. A finite-stream implementable thinning would further need a bounded-bit, capped sampler. No such full reduction is asserted.

For ordinary independent output thinning with rate t, h(z)=tz/(1-(1-t)z). Rational comparison in(R) cannot cancel the nonconstant numerator B-cs unless c=0 (the independent mask), for a,b,t strictly positive. This rejects only Bernoulli output thinning. General renewal h must be investigated separately.

## Exact spectral structure

The characteristic equation for K(u) is

    lambda^2-(A+B u)lambda+c u=0.

Generically each gap sequence is a linear combination of two powers lambda_+(u)^m and lambda_-(u)^m. Near u=1 the branches equal1 and c. Because |c|<1, one branch is locally separated, and lambda_+'(1)=a/(a+b)>0. A local analytic inverse is therefore available, in the same spirit as the actual CDRV primary PGF inverse proof. This local inverse by itself does not identify the whole observed tuple polynomial with the scalar input polynomial used in Source122.

Solving for u and the other eigenvalue gives

    u=phi(lambda)=lambda(lambda-A)/(B lambda-c),
    tau(lambda)=c(lambda-A)/(B lambda-c).

On a regular fiber these are the two eigenvalues for the same u; tau swaps the roots. For k selected positions, the channel identity has up to2^k combinations of these modes. Even though2^k is quasipolynomial when k is polylogarithmic, one observable generating function is a sum of those terms. Counting them is not inverting that sum with controlled norm. The source scalar identity uses a single independent substitution Z=q+pu per gap. Its single-strip continuation cannot be reapplied to an unidentified summand.

The fast branch is exponentially small on long gaps but not on adjacent selected positions. A long-gap/short-cluster decomposition must include exact short-gap filters with controlled observable norm and uniform errors for every positive moment completion; unobserved source gaps cannot simply be thresholded in the data. This is a candidate operation to analyze, not yet a declaration that all classical compositions fail.

## Late original-history identification

After these prefreeze calculations were written, the refined scan's operative I128 original was read at lines1–100. Its Section2.B already states EXACTLY the stationary two-state Markov target, not merely a related heterogeneous target. This is a late history read and removes any suggestion of project novelty for the target. I128 fixes rational kappa in(0,1/2], all four entries of P in[kappa,1-kappa], stationary start, known n and rational P with encoding length L, success>=2/3 for EVERY binary input, sample cap ceil exp(C_kappa(log n)^3(1+log log n)^6), and every-well-formed-stream bit cost (n+L+M)^(c_kappa). All those quantifiers and the exact budget remain unchanged. No special-chain, weaker-budget or identifiability replacement is nominated. Note02 develops additional compatibility calculations at that old scope and records why feasibility still does not close.
