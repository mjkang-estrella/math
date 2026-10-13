# I267: a sparser regime for rooted packing transfer

Parent candidate, 2026-10-12. **Unreviewed strengthening, not an accepted finding.** I248 passed correctness review I257 but received the TECHNICAL contribution verdict I258. This candidate changes its density range using classical concentration. That change alone is not asserted to meet the substantiality threshold.

## Proposed theorem

Fix d>=2. For all sufficiently large n depending only on d, let 1<=s<=10 log n be an integer, 0<r<1, and

    b=ds+binom(d,2), delta_n=n^(-1/3)(log n)^2,
    r^b>=delta_n, p=1-(1-r)^(128d).

There are deterministic typical source and target classes D for G(n,r) and E for G(n,p), with errors tending uniformly to zero, such that every G in D, H in E, root set Y with |Y|<=n^(2/3), and family R of d-slot edge-presence patterns of root degree at most s satisfies

    nu_R(H;Y)>=min{2d nu_R(G;Y), floor((n-|Y|)/(16d^2))}.       (S)

Each pattern has d distinct nonroot slots, an arbitrary prescribed internal graph, and at most s prescribed neighbors in Y at each slot. Root overlap and repetition are unrestricted. Extra edges are allowed. Nonedge constraints, candidate lists, growing d and a spanning conclusion are excluded. The family R and Y may be chosen after seeing both graphs, since the conclusion holds on D x E.

The density condition is asymptotically weaker than I248's r^b>=n^(-1/100). The target density, cap, root bound and multiplicative rank gain are unchanged. No sharp density threshold is claimed.

## 1. Compression and the common reference mean

Use the same local coordinate space as the independently validated I257 reconstruction:

    ([d] x Y) disjoint-union binom([d],2).

Close R under slot permutations. The elementary Bernoulli compression selects at most ceil(2r^(-b)) patterns such that its r-smoothed indicator is at least 1/2 on every original satisfying pattern. Closing the selected family under slot permutations gives Q of size at most M=d!ceil(2r^(-b)), subordinate to R as unordered d-block patterns. Empty R is treated separately; zero-edge patterns are allowed in compression.

For each unordered d-set U outside Y, let w_Q(U;G) be its Q-compatibility probability after independent r-addition to its local edges. Define W_Q as the maximum sum of these weights over disjoint d-sets. Let

    tau=1-(1-r)^2, mu_Q=E nu_Q(G(n,tau);Y), N=n-|Y|.

Compression and conditioning give, exactly as in I257,

    nu_R(G;Y)<=2W_Q(G;Y),
    E W_Q(G(n,r);Y)<=mu_Q,
    mu_Q>=floor(N/d)r^b>=n delta_n/(4d).                       (1)

The middle inequality is max of conditional expectations <= conditional expectation of a maximum under global independent addition. It does not use independence of different compatible blocks. The last bound uses a predetermined partition into d-sets and one required pattern per block. These steps are valid for arbitrary r; the old exponent 1/100 played no role in their proof.

## 2. Both packing functionals are (d,0)-self-bounding

Order the nonroots and partition independent graph variables into N blocks. The block X_v contains all edges from v to Y and all edges from v to later nonroots. This assigns every relevant edge once. Root-root edges are irrelevant.

Let Z denote either nu_Q or W_Q. Let Z_v be the same optimization restricted to d-sets avoiding v. It is independent of X_v: none of that block's edges enters a local pattern on a set avoiding v. Other blocks may still contain edges touching v, but those edges are ignored by Z_v and cause no problem.

For a fixed maximizing packing P, deleting its block containing v, if any, leaves a feasible packing for Z_v. For ordinary rank that block has weight one; for W_Q it has weight in [0,1]. Since restriction cannot improve an optimum,

    0<=Z-Z_v<=weight of P's block containing v<=1,
    sum_v (Z-Z_v)<=d sum_(U in P) weight(U)=dZ.                (2)

This is a genuine self-bounding estimate, stronger than the bounded-difference estimate used in I248. The optimizers need not be unique: choose one for this deterministic inequality. The finite optimization makes all functions measurable.

Apply Boucheron--Lugosi--Massart, *On concentration of self-bounding functions*, Theorem 1, with a=d and b=0. It yields

    P(Z>=EZ+t)<=exp{-t^2/[2(d EZ+((3d-1)/6)t)]},
    P(Z<=EZ-t)<=exp{-t^2/(2d EZ)}, 0<t<=EZ.                    (3)

These are credited classical inequalities, not new concentration theorems. The independent coordinate blocks may have different finite alphabets; embedding them in a common disjoint-union alphabet gives the theorem's stated common-space convention.

By (1)--(3), with conservative constants,

    P(W_Q>9mu_Q/8)<=exp{-mu_Q/(256d)},
    P(nu_Q(G(n,tau);Y)<mu_Q/2)<=exp{-mu_Q/(8d)}.               (4)

The first uses EW_Q<=mu_Q and t=mu_Q/8; the event in (4) is contained in the corresponding upper-tail event about EW_Q.

## 3. Test entropy at the new density

For each Y the labelled pattern universe has cardinality

    P_Y=2^binom(d,2) [sum_(j=0)^s binom(|Y|,j)]^d,
    log P_Y<=C_d(log n)^2.

Our hypothesis gives

    M<=3d! delta_n^(-1)=3d! n^(1/3)/(log n)^2.

Counting all root sets and all pattern families of size at most M, rather than just compressed closed ones, gives a total test count T_n with

    log T_n<=K_d[n^(2/3)log n+n^(1/3)]=:A_d(n).               (5)

Every compressed family selected adaptively from R is among these tests. Define D by W_Q<=9mu_Q/8 for all nonempty closed tests. Equations (1), (4), (5) bound its failure probability by exp{A_d(n)-n delta_n/(1024d^2)}.

## 4. Sprinkling: reveal only the needed permutation positions

Set L=64d and a=floor(N/(16d^2)). Draw L independent G(n,tau) layers. For a fixed test, independently and uniformly select a maximum Q-packing in each random host. Averaging over the host, then conditioning only on its size, makes it uniform on all matchings of that size by permutation invariance. This is not a uniformity assertion conditional on a fixed host.

Condition on every size being at least mu_Q/2. These events factor by independent layers, and their joint failure probability is at most L exp{-mu_Q/(8d)}. Uniformly trim each matching to

    q=floor(min{mu_Q/2,a}).

The trimmed matchings are independent uniform q-matchings. At a step before accumulating a blocks, the occupied set B has size less than N/(16d). The next q-matching is independent of this past. Generate it by grouping the first dq entries of a uniform permutation of the N vertices. Let X_B count its blocks avoiding B. Then E X_B>=15q/16.

Expose only those dq positions, not all N positions. A prefix-preserving transposition couples two choices of the next entry and changes at most two block indicators. Thus each Doob increment has absolute value at most two, and after dq exposures the entire function is known. The elementary Azuma bound gives

    P(X_B<q/2)<=exp{-49q/(2048d)}<=exp{-q/(64d)}.              (6)

This shorter martingale is the second improvement over I248, whose weaker estimate used N exposures and exponent q^2/N. Both arguments are valid, but (6) is needed at the new supply scale. No independence of positional blocks is assumed.

For large n, mu_Q>=6, a>=2, and

    q>=n delta_n/(64d^2).                                   (7)

Indeed, if mu_Q/2<=a, then q>=mu_Q/3; otherwise q=a>=N/(32d^2). Equation (7) follows from (1), N>=n/2 and delta_n<=1.

Process layers retaining blocks that avoid the currently occupied vertices, stopping at a. Conditional union bounds and (6) cost at most L exp{-q/(64d)}. The old floor arithmetic remains unchanged: in the uncapped case Lq/2>8d mu_Q; when q=a, two successful rounds suffice to hit the cap. Hence the union host satisfies

    nu_Q(H;Y)>=min{8d mu_Q,a}                                (8)

except on a set of probability at most L exp{-mu_Q/(8d)}+L exp{-q/(64d)}. Its distribution is exactly G(n,p).

Define E by (8) for every test. A failure in the union host forces failure of every auxiliary matching witness, so the joint witness bound also bounds the host's marginal failure probability. Equations (1), (5), (7) give the common uniform error bound

    min{1,(1+2L) exp(A_d(n)-c_d n^(2/3)(log n)^2)},
    c_d=1/(4096d^3).

It tends to zero. In particular the test entropy is dominated even at the lower endpoint r^b=delta_n.

## 5. Transfer, limits and contribution status

For every G in D, H in E and adaptively selected R,Y, its compression Q gives

    nu_R(G;Y)<=9mu_Q/4,
    nu_R(H;Y)>=nu_Q(H;Y)>=min{8d mu_Q,a}
                              >=min{2d nu_R(G;Y),a}.

This proves the proposed (S). Empty families have rank zero. All parameter cutoffs and errors depend only on fixed d. The bounded-component embedding application from I248 follows with the identical padding and Aharoni--Haxell calculation in the validated I257 reconstruction; it is not another nomination.

The supplied argument does not reach a claimed optimal rooted-density threshold. The new threshold is still determined by a coarse mean lower bound and uniform root/test entropy. The substantiality objection in I258 must be reconsidered against this actual range, not assumed resolved: the improvement uses a classical self-bounding theorem and a more economical permutation exposure. No new structural or candidate-list method has been proved. Independent correctness and contribution reviews have not run for I267.
