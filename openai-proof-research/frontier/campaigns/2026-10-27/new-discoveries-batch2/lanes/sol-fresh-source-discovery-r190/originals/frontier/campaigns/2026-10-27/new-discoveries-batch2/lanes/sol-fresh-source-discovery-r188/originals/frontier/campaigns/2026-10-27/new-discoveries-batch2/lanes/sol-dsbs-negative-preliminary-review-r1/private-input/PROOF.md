# Negative-order DSBS common information: complete ordinary proof candidate

Status: ordinary mathematics only, eligibility/source-prior HOLD, credit 0. No Lean or manuscript. This is a full-source candidate, not a finite diagnostic, helper nomination, or a claimed worldwide first. All logarithms below are base 2; ln denotes the natural logarithm.

## Attribution and exact scope

Lei Yu, *Rényi Common Information for Doubly Symmetric Binary Sources*, arXiv:2407.06132v1, 8 July 2024, Section II, Conjecture 1, equation (19). The actual primary body defines the uniform common seed and arbitrary block processors in equations (6)–(11), and explicitly asks for strict separation from Wyner's value for sufficiently negative orders and sufficiently small crossover probability. Latest arXiv abstract still lists v1. The actual text, not only the abstract, is retained in sources/dsbs.html and its faithful cleaned extraction.

We prove the precise stronger quantifier statement

    for every 0 < e <= 1/1024 and every beta in [1,infinity],
    Ttilde_{-beta}(DSBS(e)) > 1 + H(e) - 2 H((1-sqrt(1-2e))/2).

The infinity case means order -infinity. No assertion is made at e=0 or e=1/2. The source's decimal numerical phase threshold is not identified or claimed sharp. The source does not prescribe a numeric beta threshold; our beta>=1 is sufficient.

We use its established Proposition 1, equations (20)–(21), for the exact relaxed Wyner information of a DSBS, together with the ordinary Shannon entropy chain rule and the variational formula proved below. Proposition 1 is attributed to the mutual-information-region theorem of Yu, IEEE TIT 69(10) (2023), 6251–6268, DOI 10.1109/TIT.2023.3293616, arXiv:2212.14696v2. This nontrivial input is not recredited as our theorem. The general achievability bound in the 2024 source is not needed for strict separation.

## 1. A finite-block change-of-measure converse

For a joint law Q on finite X times Y, put

    C(Q,t) = inf { I_Q(XY;W) : I_Q(X;Y|W) <= t }.

The infimum is over all conditional laws W|XY, without conditional independence imposed. This is exactly the source's relaxed Wyner definition.

Fix beta>0, a fully supported target pi, and a block synthesis law

    P_n(x^n,y^n) = (1/M) sum_m A_m(x^n) B_m(y^n).

No coordinate factorization of A_m or B_m is assumed. Put c=1+1/beta and E_n=D_{1+beta}(pi^n || P_n). For every joint Q and every n with E_n finite, we claim

    (log M)/n >= C(Q, c D(Q||pi) + E_n/n).                 (A)

If E_n is infinite infinitely often, the code sequence cannot achieve a vanishing normalized divergence; those blocks need not be considered.

First, for any distributions S,T,V with the indicated divergences finite,

    D(S||V) - c D(S||T) <= D_{1+beta}(T||V).              (B)

Indeed let Z=sum_z T(z)^{1+beta} V(z)^{-beta}, and let
R(z)=T(z)^{1+beta} V(z)^{-beta}/Z. Direct substitution gives

    D(S||V)-cD(S||T) = (log Z)/beta - D(S||R)/beta.

Nonnegativity of KL proves (B). Taking S=Q^n,T=pi^n,V=P_n gives

    D(Q^n||P_n) <= c n D(Q||pi) + E_n.                  (C)

Transport the posterior of the synthesis seed: define the joint law

    Qhat(m,x^n,y^n) = Q^n(x^n,y^n) P_n(m|x^n,y^n).

Its XY marginal is exactly the independent-coordinate Q^n. Its divergence from the original joint synthesis law equals D(Q^n||P_n), by cancellation of the identical posterior. By the KL chain rule and conditional independence under the original law,

    D(Q^n||P_n)
      = D(Qhat_M||Unif[M])
        + I_Qhat(X^n;Y^n|M)
        + sum_m Qhat_M(m) [D(Qhat_{X^n|m}||A_m)
                          +D(Qhat_{Y^n|m}||B_m)]
      >= I_Qhat(X^n;Y^n|M).                            (D)

Zeros cause no difficulty: pi is fully supported and E_n finite forces P_n fully supported; posterior transport is then defined everywhere. A component of zero mass can be omitted, and all terms with positive Qhat mass have original support.

Let U_i=(X_i,Y_i) and W_i=(M,U_1,...,U_{i-1}). Independence of the U_i under Qhat and the entropy chain rule give

    sum_i I(U_i;W_i) = I(U^n;M) <= H(M) <= log M.       (E)

Also conditioning decreases entropy, hence

    sum_i I(X_i;Y_i|W_i)
      = sum_i [H(X_i|M,U_{<i})+H(Y_i|M,U_{<i})
               -H(U_i|M,U_{<i})]
      <= H(X^n|M)+H(Y^n|M)-H(U^n|M)
      = I(X^n;Y^n|M).                                 (F)

Take an independent uniform index J and W=(J,W_J). The marginal U_J is Q and is independent of J, so (E) implies I(U_J;W)<=log M/n. Equations (C),(D),(F) imply I(X_J;Y_J|W)<=cD(Q||pi)+E_n/n. This conditional law is feasible in C, proving (A).

The value C(Q,t) is right continuous in t>=0: support reduction preserves the XY marginal (d-1 coordinates, d=|X||Y|), the average conditional mutual information, and average conditional joint entropy. Caratheodory gives at most d+2 atoms of W. The resulting finite compact simplex and continuity of entropy imply that any optimizing sequence at t_k decreasing to t has a feasible limit at t; monotonicity supplies the reverse inequality. The same subsequence argument handles arbitrary t_k>=t with t_k -> t.

For a normalized achievable code sequence E_n/n -> 0, (A) thus implies

    R >= C(Q,cD(Q||pi)) for every Q.                   (G)

The source's skew symmetry converts vanishing D_{-beta}(P_n||pi^n)/n to E_n/n ->0, since D_{-beta}=-beta/(1+beta) D_{1+beta}(pi^n||P_n). Therefore (G) is a lower bound on Ttilde_{-beta}. It applies uniformly to every block code and every block length, not to a restricted iid code ensemble.

## 2. A strict perturbation of a DSBS

Write h=H, s=sqrt(1-2r), a=(1-s)/2, b=a^2/(a^2+(1-a)^2), and L=log((1-a)/a). Denote Wyner's value by

    w(r)=1+h(r)-2h(a).

The source's Proposition 1 gives, for t sufficiently small and nonnegative,

    C(DSBS(r),t)=(1-r)(1-h(q)),
    t=F(r,q):=2h((1-r)q+r/2)-(1-r)h(q)-r-h(r),

where q is on the branch q>=b. At q=b, one has (1-r)b+r/2=a, F=0, F_q=0, and

    F_qq(r,b) = 4(1-r)^2(1-2r)/(r^2 ln 2) >0.         (H)

These identities follow from a(1-a)=r/2,
b(1-b)=r^2/[4(1-r)^2], h'(x)=log((1-x)/x),
and h''(x)=-1/[x(1-x)ln2]. Furthermore

    w'(r)=log((1-r)/r)-L/s.

Fix e in (0,1/2) and c>0. Set r=e-delta with delta decreasing to zero. The binary KL expansion is

    D(r||e)=delta^2/[2 e(1-e)ln2]+O(delta^3).

Smooth Taylor expansion of F about its quadratic minimum, uniformly for r near e, gives for t=cD(r||e) the right branch

    q-b(r) = delta sqrt(c/[e(1-e)ln2 F_qq(e,b(e))])
              +o(delta).

This is valid because F_qq is strictly positive; F is strictly increasing immediately to the right of b. The branch in Proposition 1 is exactly this local branch. Expanding (1-r)(1-h(q)) along it yields

    C(DSBS(e-delta), cD(e-delta||e))
      = w(e) + [ A(e)-sqrt(c) B(e) ] delta + o(delta),  (I)

where, with s=sqrt(1-2e) and L=log((1+s)^2/(2e)),

    A(e)=L/s-log((1-e)/e),
    B(e)=L sqrt(e/[(1-e)(1-2e)]).

No sign conclusion about the actual common information is obtained merely from the source's achievability upper bound. The essential new bridge is the converse (G); (I) is applied to that lower bound.

## 3. Explicit interval, all orders beta>=1

For 0<e<=1/1024, s>31/32. Therefore

    A(e) >= L-log((1-e)/e)
         = log((1+s)^2/[2(1-e)])
         > log(7/4) > 3/4.

The first strict bound follows because (63/32)^2/2=3969/2048>7/4; the second because (7/4)^4>8. On this interval sqrt(e) log(2/e) is increasing: its derivative has the sign of ln(2/e)-2>0. Also L<=log(2/e), and sqrt((1-e)(1-2e))>3/4. Consequently

    B(e) < (4/3) (11/32) = 11/24.

For every finite beta>=1 we have c=1+1/beta<=2 and sqrt(c)<=sqrt2<3/2, whence

    A(e)-sqrt(c)B(e) > 3/4-11/16 = 1/16 >0.           (J)

For each e and beta choose delta sufficiently small and positive in (I). Equations (I),(J) then give C(DSBS(e-delta),cD(e-delta||e))>w(e). By (G), Ttilde_{-beta}(DSBS(e)) exceeds w(e). This proves every stated finite-beta case. For beta=infinity, D_infinity(pi^n||P_n)>=D_2(pi^n||P_n), so any code achievable at order -infinity is achievable at order -1 under the reverse formulation. Thus Ttilde_{-infinity}>=Ttilde_{-1}>w(e). The proof is complete.

## Strongest complete-adaptation objection and falsifiers

The entire bridge is now exhibited: classical Renyi/KL variational identity (B), exact seed-posterior KL chain rule (D), classical independent-coordinate entropy tensorization (E)–(F), the already-public exact relaxed Wyner formula, and its quadratic perturbation (H)–(J). A competent reviewer could judge this a routine application of classical change of measure and the published mutual-information region. Classical tools alone do not settle that judgment, but this complete bridge makes the objection concrete. Eligibility stays HOLD; no count or acceptance is requested from this lane.

The mathematical candidate is falsified if (D) fails for an arbitrary correlated-block processor, if (F) has the wrong inequality direction, if the source's Proposition 1 has a different local optimizing branch than q>=b, or if an actual public theorem already supplies (G) for common-information codes. The first three have explicit algebraic derivations above and bounded diagnostics; independent adversarial review is still necessary. The last would be a prior/adaptation exclusion, not a mathematical counterexample. No registry path-absence claim resolves it.
