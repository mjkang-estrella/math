# Dorward 345816: full-scope route, unresolved

No full solution. No novelty or significance claim for the reductions or restricted cases below.

Primary: Robert Dorward, *Combinatorial statistics on restricted growth functions containing a pattern exactly k times*, arXiv:2003.05073v1 (11 March 2020). The live abstract lists only v1. Downloaded current PDF hash and time in fetch-receipts.json; actual printed pp.10–11 (Proposition 3.5), pp.15–17 (Conjectures 4.1/4.2), pp.18–21 (the classical linear-algebra route and its limitations) were read. This is a thesis/preprint, not independently established as a refereed journal statement; significance/source-publication objections remain. The accompanying larger Sperner conjecture is not the target here.

Exact object: a restricted growth word w of length n has w_1=1 and w_i<=1+max(w_1,...,w_{i-1}). Containment of 112 counts index triples i<j<k with w_i=w_j<w_k. R_(n,1)(112) contains precisely those words with exactly one such triple. The statistic ls(w) counts, for each position, distinct smaller values appearing earlier, and sums these counts; for a restricted growth word it equals sum_i(w_i-1). The target is: for every integer n>=3 the coefficients of F_n(q)=sum_(w in R_(n,1)(112)) q^ls(w) are unimodal. Empty n<3 cases give the zero polynomial. Unimodal means weakly increasing up to some index and weakly decreasing thereafter, including all internal zero coefficients. Proposition 3.5 supplies the exact identity

    F_(m+2)(q) = q [m]_q product_(i=2..m)(1+q^i), m>=1.

Here [a]_q=1+q+...+q^(a-1), with empty products one. Thus q can be removed without changing unimodality. No domain discrepancy is used.

## All-parameter algebra and the exact unpaid inequality

Put Q_m=F_(m+2)/q, P_(m-1)=product_(i=1..m-1)(1+q^i), and B_m=product_(i=2..m-1)(1+q^i), for m>=2. Using (1+q^m)[m]_q=[2m]_q and (1+q)[m]_(q^2)=[2m]_q gives identically

    Q_m = [m]_(q^2) P_(m-1) = [2m]_q B_m.

The degree D of B_m is m(m-1)/2-1; Q_m has degree D+2m-1. Let b_m(t) be the number of subsets S of {2,...,m-1} with sum t, zero outside 0<=t<=D. Complementing subsets proves b_m(t)=b_m(D-t). Write a_m(k) for the coefficient of Q_m. Multiplication by [2m] and telescoping give

    a_m(k)-a_m(k-1) = b_m(k)-b_m(k-2m).

All factors are palindromic, so Q_m is palindromic. Consequently the full source conjecture is equivalent, for every m>=2, to

    b_m(k) >= b_m(k-2m)
    for every integer 1<=k<=floor((D+2m-1)/2).

The m=1 case is Q_1=1. This is a literal equivalence, not an asymptotic reduction. The range k<2m is immediate. The remaining moving window around the middle is unpaid. Computing these coefficients does not prove the universal inequality.

## Classical symmetric-chain-character route and its exact limit

The source's Theorem 4.4 states the classical Hughes unimodality of P_r. For a symmetric unimodal polynomial P of degree d, with coefficients p_j, telescoping gives its elementary expansion

    P = sum_(j=0..floor(d/2)) c_j q^j [d-2j+1]_q,
    c_j=p_j-p_(j-1)>=0 (p_(-1)=0).

Proof: the coefficient of q^k up to the middle is sum_(j<=k)c_j=p_k, and symmetry proves the other half.

If d is odd, every displayed interval has even length 2a. Now

    [2a]_q [m]_(q^2) = (1+q)[a]_(q^2)[m]_(q^2).

The coefficients of [a]_u[m]_u count pairs of bounded nonnegative integers of given sum: they increase by one, then are constant, then decrease by one, symmetrically. Substituting u=q^2 and multiplying by 1+q repeats each coefficient twice. Hence this polynomial is symmetric unimodal. In the expansion of P each shifted summand has the common center (d+2m-2)/2; a nonnegative sum of such polynomials is unimodal. Applying the source-known theorem to P_(m-1) proves Q_m unimodal whenever m(m-1)/2 is odd, i.e. m=2 or 3 modulo4. This is a routine partial consequence and gets zero credit; it is not advanced as a new result or a full solution.

For d even the intervals have odd lengths L. The parity-free lemma is false: [3]_q[3]_(q^2) has coefficients (1,1,2,1,2,1,1). In particular even a symmetric unimodal input does not suffice. The exact contribution of a chain starting at j to the first difference is

    c_j q^j (1-q^L) sum_(r=0..m-1) q^(2r).

Short odd intervals L<2m-1 can have negative contributions before the common center. Thus m=0,1 modulo4 requires cancellation between actual Hughes-chain multiplicities c_j; nonnegativity of each c_j alone cannot close it. Long odd intervals L>=2m-1 have no negative contribution before their center. No proof of the required cancellation for the short intervals was obtained.

## Attempted full-scope subset injection and rigorous obstruction

A natural construction for the unpaid inequality takes a source subset S of weight k-2m and adds a disjoint subset T of unused parts of total weight 2m. This would require an injective deterministic choice of T, and even pointwise existence fails.

Take m=13, S={3,4,5,6,7}, sum S=25. Here D=77, k=51, and floor((D+25)/2)=51, so this is exactly inside the required range. The unused parts are {2,8,9,10,11,12}. No subset of them has sum26: with at most two of the five large parts, the sum is at most11+12+2=25; with at least three, the sum is at least8+9+10=27. Thus no purely additive inclusion-preserving injection can prove the full inequality. This does not refute the inequality: a valid injection may delete and replace parts. Nor does it prove failure of an arbitrary matching between the two weight classes.

The same pointwise obstruction occurs in the finite diagnostic at m=16 with S={3,...,9}, sum42, target74 and unused {2,10,...,15}; this second instance gets no credit.

The next concrete mechanism is a replacement injection or a chain-multiplicity cancellation theorem for precisely the short odd chains. Any replacement algorithm must carry recoverable state so different source subsets cannot merge, must change the sum by exactly2m, and must work uniformly up to the moving central endpoint. No such algorithm or cancellation inequality is presently available. This is the precise gap, not a claim that another finite scan is a proof strategy.

## Exact diagnostics and Lean feasibility

Run `python -I exact_diagnostic.py`. The script uses only Python integers, with 60 CPU seconds and 512MiB address space caps. It checks both product formulas independently for m=1..120, their coefficient monotonicity, nonnegative Hughes-chain multiplicities, 900 even-chain controls, and the generic odd-chain obstruction. A separate bitset subset-sum loop checks every relevant source subset for m=4..18 until its first failed additive extension; it records actual input/output and the m13 witness. The source already reports checks through n=800, so this smaller run adds no computational-progress credit. Results are exact implementation diagnostics, not proofs of unresolved all-m claims.

The finite polynomial identities, symmetric expansion and even-chain lemma fit ordinary Mathlib polynomials/finite sums and elementary inequalities. A full Lean endpoint would need the actual restricted-growth-word statistic generating function, its source bijection/product identity, and the remaining all-m subset-count inequality. It cannot declare the coefficient formula to be the original combinatorial object without proving that bridge. There is no complete ordinary endpoint and therefore no residual-bridge-free Lean theorem proposed. No formal implementation was made.
