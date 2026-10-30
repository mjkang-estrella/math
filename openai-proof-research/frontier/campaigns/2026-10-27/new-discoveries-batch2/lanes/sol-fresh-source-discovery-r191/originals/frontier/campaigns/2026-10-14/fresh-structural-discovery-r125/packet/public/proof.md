# T238B125: full author proof at the unchanged scope

This is an author argument relative to the stipulated pinned inputs. It is not an independent correctness or contribution verdict. FROZEN-SCOPE.md remains authoritative. No downstream manuscript or formalization is claimed.

## 1. Exact input and conventions

Let U_n denote uniform measure on S_n. A permutation maps input positions to output positions; products apply the right factor first. Fourier averages in unitary irreducibles multiply under convolution. Write D_lambda for an irreducible dimension and use unnormalized Schatten norms. Total variation is one half the l1 distance of probability masses.

The essential pinned input is **Conditional coordinate sweeps and analytic transfer**, source238, `build/sections/03-paths.tex`, Theorem `thm:conditional` / `ac:main`, equation `ac:eq:15`, at z=0. Its absolute parameters are a power of two R, an integer q>=1 and c0=e0=1/10000. The ordered product grid has coordinate sizes m_j in [R,R^2], all powers of two, and total size n. On each stage-line independently choose a uniform permutation. A specified family H of h labelled paths has distinct slots at every layer. The paths are determined by their two endpoints. On the n-h free slots the conditional average K_mu^H satisfies

    log ||K_mu^H||_(2q)^(2q)
       <= -c(n) log D_mu + e(n) h log n - C(H),

where c(n)>=c0, e(n)<=e0 and C(H)>=0. This is an input for every feasible fixed path family, not merely one chosen independently of the sweep. Put

    a=c0/(2q)>0, b=e0/(2q)>0, M=R^2, B=(a+b)M.

The immediate input consequence is

    ||K_mu^H||_op <= D_mu^(-a) n^(b h).                 (1)

The source proves the moment bound through its conditional induction; no upstream proof is audited here. Its `02-preliminaries.tex` gives the branching and dimension facts used below, and `07-analytic.tex` gives the fixed-segment analytic/Fourier route. The present proof must retain the original line laws at the final parameter; no near-fair replacement is made.

## 2. A bound for the full conditional permutation

Fix lambda partitioning n and a feasible H of h paths. The full permutation under this conditioning lies in a left/right translate of S_(n-h), fixing the prescribed input-output pairs. Under fixed identifications its average in [lambda] differs by left/right unitaries from the average of the residual law in the restricted representation. Restriction is an orthogonal direct sum of irreducibles [mu] of S_(n-h), with multiplicities. Consequently its operator norm is the maximum of ||K_mu^H|| over occurring mu.

For every such constituent,

    D_lambda <= (n)_h D_mu <= n^h D_mu.               (2)

For completeness the first inequality needs no choice of a largest constituent. Frobenius reciprocity says [lambda] occurs in Ind_(S_(n-h))^(S_n)[mu] whenever [mu] occurs in the restriction. That induced representation has dimension (n)_h D_mu. One can see the needed injection directly: for a nonzero subgroup intertwiner T:[lambda]->[mu], map v to the function g->T rho_lambda(g)v. It is determined by its values on the (n)_h cosets, and its kernel is invariant under S_n; irreducibility and nonzero T make the kernel zero. This proves (2) for EVERY constituent, including n-h=0.

Combining (1) and (2) yields for the full conditional average A_lambda^H

    ||A_lambda^H||_op <= D_lambda^(-a) n^((a+b)h).    (3)

It is also a contraction. No invariant subspace is chosen depending on the eventual biased sweep.

## 3. Replacing specified lines: exact path disintegration

Fix a set F of k stage-lines. Replace the uniform law on each L in F by any probability Q_L on S_|L|, independently. Leave every other line uniform. There is no bound on the density of Q_L needed in this step.

Work first under the all-uniform independent-line network. For a realization omega, record the set A(omega) of input labels whose paths traverse at least one line in F, and the complete endpoints of all these labels. Call this record H(omega). The coordinate order reconstructs all intermediate slots. At most M k distinct labels are recorded, so h=|A|<=Mk (also h<=n).

**Cylinder identity.** For any realized record H, the event {H(omega)=H} equals the event that the fixed labelled paths in H occur. One implication is immediate. Conversely, in that realized record, the paths cover every input slot of each line in F, because the record includes every card that used the line. If these fixed paths occur in another network realization, injectivity prevents any other label from using an input slot of any line in F. Every recorded label still traverses F, since that fact is determined by its path. Thus the selected set of labels and all its paths are exactly H. This proves both directions; selection by the realized routing adds no hidden conditioning.

The Radon–Nikodym derivative of the modified independent-line network with respect to the uniform one is

    w(omega)= product_(L in F) |L|! Q_L(g_L(omega)).

On a record H the entire permutation g_L on each L in F is fixed: all its input slots and their output assignments are recorded. Hence w is constant on that record. For any record of positive modified probability, the conditional network law given that record is therefore exactly the all-uniform network law conditioned on its fixed paths. The full modified permutation law is a convex mixture of these conditional laws. This statement also covers Q_L with zeros.

Apply (3) to every component and use h<=Mk. If A_lambda(F) is the Fourier average of the modified sweep, then

    ||A_lambda(F)||_op <= D_lambda^(-a) n^(Bk).        (4)

The right side can exceed1, in which case it is merely a valid bound. Revealing arbitrary local coin values without covering their lines would not justify this argument; full-slot coverage is essential.

## 4. A small interval for arbitrary perturbation laws

For every line choose Q_L, and interpolate independently by

    L_L(z)=(1-z)U_|L|+zQ_L.

For real 0<=z<=1, condition on the random subset of replaced lines. Let L_total be the total number of stage-lines. Since each coordinate has at least two values,

    L_total=sum_j n/m_j <= n log_2 n <= n^2.

Averaging (4) with the independent Bernoulli(z) subset probabilities gives

    ||K_lambda(z)||_op
       <= D_lambda^(-a) (1-z+z n^B)^L_total
       <= D_lambda^(-a) exp(L_total z n^B).           (5)

Define eta_n=1/(8 n^(B+2)). On 0<=z<=2eta_n, (5) is at most e^(1/4)D_lambda^(-a).

For all sufficiently large n, every S_n irreducible except the trivial and sign representations has log D_lambda>=1/(2a). Here is a quantitative input sufficient for that statement and later summation: source `02-preliminaries.tex` gives, with k=min(n-lambda_1,n-lambda'_1),

    D_lambda >= e^(-1) binom(n,k)  when 1<=k<=n/3,
    log D_lambda >= c_dim n        when k>n/3,

for an absolute c_dim>0 in the second range and all sufficiently large n. Thus D_lambda>=n/e for all these representations once n is sufficiently large. The finitely many excluded dimensions are dealt with in Section8. Therefore, for large n and every nontrivial, nonsign lambda,

    ||K_lambda(z)||_op <= D_lambda^(-a/2)
                 for z in [eta_n,2eta_n].            (6)

This shrinking interval is deliberate. A fixed nonzero biased one-card eigenvalue prevents a dimension-power bound on a fixed interval when uniform one-card marginals are absent.

## 5. Uniform complex disk for the actual bounded-bias laws

Fix delta in (0,1/2). Let Q_L now be one binary sweep inside a line of size m in [R,R^2], with independent switch probabilities that can be different at every switch but lie in [delta,1-delta]. These probabilities are deterministic. Only finitely many line sizes occur.

In a unitary representation, a single switch with transposition tau averages to A_p=(1-p)I+p rho(tau). Its fixed subspace has eigenvalue1 and its orthogonal complement has eigenvalue1-2p of absolute value at most1-2delta<1. A line sweep is a finite product of these contractions. In a nontrivial irreducible of S_m that product has norm strictly less than1: a norm-attaining unit vector at norm1 would preserve its norm at every factor and hence be fixed by every transposition used. The intermediate vector then never changes. The used cube-edge transpositions generate S_m, forcing an invariant vector in a nontrivial irreducible, a contradiction.

The product operator depends continuously on the finitely many probabilities. Compactness of their cube [delta,1-delta]^J, and finiteness of the line sizes and irreducibles, give one number kappa_delta<1 bounding all these nontrivial norms. This uniformity includes spatially varying probabilities and different lines. Choose a fixed r_delta>1 with r_delta*kappa_delta<1 (if kappa_delta=0, take r_delta=2).

Let P be uniform averaging on a line and Q its actual line average in an arbitrary unitary representation restricted to that line subgroup. Uniform averaging absorbs Q: PQ=QP=P. Relative to line invariants and their orthogonal complement,

    (1-z)P+zQ = I on invariants, and zQ off invariants.

Every nontrivial block of Q is bounded by kappa_delta, with arbitrary multiplicities. Thus the interpolated line operator is contractive for |z|<=r_delta. Products over lines and stages imply

    ||K_lambda(z)||_op <=1  for |z|<=r_delta.          (7)

The sweep average is a matrix polynomial in z. Its degree may grow with n, but (7) is independent of the degree, grid, schedule and representation. No probabilities at a complex z are interpreted as a stochastic process.

## 6. Shrinking-segment analytic transfer

Write r=r_delta and eta=eta_n. For t in [eta,2eta], use the disk Green kernel

    g_r(z,t)=log |(r^2-tz)/(r(z-t))|.

For large n, 2eta<1/2. The kernel is harmonic on |z|<r away from z=t, nonnegative there, and zero when |z|=r. Its numerator has no zero in the disk. Define

    V(z)=(1/eta) integral_eta^(2eta) g_r(z,t) dt,
    H_n=log(r/eta)+2,  W(z)=V(z)/H_n.

The logarithmic singularity is integrable; V extends continuously to the slit and its endpoints. On the circle V=0. For x in the slit, the numerator/r is at most r, and after scaling t=eta u, x=eta v,

    V(x) <= log(r/eta) + integral_1^2 -log|v-u| du
          <= log(r/eta)+1+log2 < H_n.

The integral is maximized at v=3/2, as follows either by differentiating or by its expression 1-l log l-(1-l)log(1-l), l=v-1 in [0,1], with 0log0=0. Consequently W<=1 on the slit. At z=1,

    (r^2-t)/(r(1-t)) >=r,

so V(1)>=log r and W(1)>=log r/H_n.

For unit vectors u,v let f(z)=u^*K_lambda(z)v. If f is not identically zero, log|f| is subharmonic, including value minus infinity at zeros. On the disk minus the slit, put

    A=(a/2)log D_lambda,  J(z)=log|f(z)|+A W(z).

By (6) its boundary limsup on the slit is at most -A+A=0; by (7) and W=0 its boundary limsup on the circle is at most0. The boundary maximum principle gives J<=0. If f is identically zero the resulting inequality is automatic. Taking the supremum over unit u,v gives

    ||K_lambda(1)||_op
       <= exp[- a log r * log D_lambda /(2 H_n)].     (8)

Since

    H_n=(B+2)log n + log(8r)+2,

there is gamma_delta>0, depending only on delta and the fixed source constants, such that for all sufficiently large n,

    ||K_lambda(1)||_op <= D_lambda^(-gamma_delta/log n)
                    (lambda neither trivial nor sign).     (9)

For example gamma_delta=a log r/(2[B+2+(log(8r)+2)/log2]) works whenever the preceding large-n conditions hold. The Green-kernel normalization matters: directly shrinking the source's specific uncorrected logarithmic barrier would give a weaker estimate.

## 7. Full permutation mixing, different sweeps, and all error tolerances

For d>=log_2 R, group consecutive bits into blocks as the source does: write d=b0*l+t with l=log_2 R and 0<=t<l; take one block of l+t bits and b0-1 blocks of l bits. The block sizes lie in [R,R^2]. Within a block, different coarse lines use disjoint coin sets; their sweeps are independent. This identification works with arbitrary deterministic switch probabilities, because the actual order of bits is retained. At z=1 the product-grid sweep is exactly one full d-step sweep of the prescribed biased process in the nonrotating frame.

For each sweep j let K_(lambda,j) be its Fourier matrix. Bound (9) is uniform in every probability in every line, so for s complete sweeps

    ||K_(lambda,s)...K_(lambda,1)||_op
            <= D_lambda^(-gamma_delta s/log n).      (10)

No common eigenbasis, normality, equality of distributions, or stationarity in time has been used.

The sign coefficient of a whole binary sweep is the product over its nd/2 switches of (1-2p). Thus its absolute value is at most r0^(nd/2), r0=1-2delta<1; over s sweeps it is at most r0^(snd/2). The trivial coefficient is1. Finite-group Plancherel and Cauchy–Schwarz give

    4 TV_s^2 <= r0^(snd) +
       sum_(lambda neither trivial nor sign) D_lambda^(2-2gamma_delta s/log n). (11)

Here Frobenius norm squared is bounded by dimension times operator norm squared, and the other factor D_lambda is the regular multiplicity. An initial deterministic permutation only multiplies Fourier matrices by unitaries.

We give a uniform quantitative bound for the sum. Choose an absolute beta0 so large that

    2*3^(-beta0)<1 and beta0*c_dim>log2+1.

There are at most 2*2^k diagrams with k=min(n-lambda_1,n-lambda'_1)<=n/3. The source's binomial bound and binom(n,k)>=(n/k)^k show

    sum_(1<=k<=n/3) D_lambda^(-beta0)
       <= 2e^beta0 sum_(k>=1) [2*3^(-beta0)]^k.

For k>n/3, at most2^n partitions and the large-dimension bound give a sum at most e^(-n). Hence the entire sum is bounded by an absolute C0 for all sufficiently large n. Also every such D_lambda>=n/e. Take

    s0=ceil((beta0+2)log n/(2gamma_delta)).

At s0 the sum in (11) is at most C0. For s=s0+u, each further sweep reduces its upper bound by a factor at most exp(-gamma_delta), because log(n/e)>=log n/2 for large n. Thus

    4 TV_s^2 <= r0^(snd)+C0 exp(-gamma_delta u).      (12)

Choosing s>=C_delta*(d+log(1/epsilon)) with C_delta sufficiently large makes both terms at most2epsilon^2, simultaneously for all 0<epsilon<=1/4. The sign term already has nd>=2, and is bounded by exp(-2[-log r0]s). The choice of C_delta depends only on delta and absolute source constants. Enlarging it handles integer ceilings. This proves the displayed full bound for all sufficiently large d.

## 8. All finite dimensions and arbitrary later times

The preceding thresholds are finite and independent of the schedule. For each of the finitely many smaller d, use a direct uniform minorization. In a complete sweep there are K_d=nd/2 independent coins. The event that they realize any fixed mask has probability at least delta^K_d. In particular the sweep can realize the identity, or any single cube-edge transposition, with probability at least delta^K_d.

Any transposition of two cube vertices is a word of at most2d-1 edge transpositions: traverse a shortest path and return without repeating its last edge. Any permutation is a product of at most n-1 arbitrary transpositions. Thus every element of S_n is represented by at most

    H_d=(n-1)(2d-1)

cube-edge transpositions. Pad with identities. In H_d complete sweeps, under ANY of the allowed time-dependent arrays, each prescribed permutation consequently has probability at least a_d=delta^(K_d H_d). Distinct resulting permutations correspond to disjoint events, so beta_d=n! a_d<=1, and the block kernel dominates beta_d U_n from every initial state.

Every step preserves U_n. Iterating these block minorizations gives TV at most (1-beta_d)^floor(s/H_d), and hence at most exp[-beta_d floor(s/H_d)] after s sweeps. If beta_d=1 convergence in one block is immediate. The finitely many dimensions permit a single enlargement of C_delta making this bound at most epsilon whenever s>=C_delta*(d+log(1/epsilon)). This includes d=1. Constants may be enormous; no effective-size assertion was frozen.

At times divisible by d the deterministic coordinate rotation is the identity. Undoing it at other times is a deterministic permutation of positions and preserves distance to uniform. Moreover, each subsequent update is a random permutation independent of the current deck, so it fixes uniform measure and contracts total variation, even though its law changes with time. Thus the bound at

    d*ceil(C_delta*(d+log(1/epsilon)))

holds at every later integer time. This completes the entire frozen upper theorem.

## 9. Credited sharpness

Structuralr113 `packet/public/screen-238.md` already contains the following complete calculation, using the classical eigenfunction/second-moment method. In the homogeneous case p!=1/2, let rho=1-2p, r=|rho|, and give each card the sign of its initial first coordinate. For the signed matching statistic F at sweep endpoints,

    E F_s=n rho^s, Var(F_s)<=2n,
    E_U F=0, Var_U(F)=n^2/(n-1).

The other coordinate updates leave F unchanged pathwise; the first-coordinate update multiplies its conditional mean by rho and adds conditional variance at most8np(1-p). This proves the displayed recursion and bounds. Chebyshev applied to sign(rho^s)F>=n r^s/2 gives

    TV_s >=1-8/(n r^(2s))-4/((n-1)r^(2s)).

If s<= (1-alpha)log n/(-2log r), then n r^(2s)>=n^alpha, so this lower bound tends to1. It is valid for both signs of rho, including s=0. Choosing delta<min(p,1-p) permits application of the just-proved upper bound. Fixed-error mixing therefore has order Theta_p(d^2). This is the exact old lower calculation coupled to the new author upper argument, not another proposed contribution.

## 10. Limits

All pinned source contracts are assumed, not re-proved. The proof does not establish a result for probabilities selected after observing the deck, dependent coins, unboundedly small probabilities, altered coordinate schedules, or nondyadic deck sizes. These are outside the frozen statement. Integrity checks and any finite tests are not mathematical gates. Independent full-scope proof and contribution reviews remain necessary.
