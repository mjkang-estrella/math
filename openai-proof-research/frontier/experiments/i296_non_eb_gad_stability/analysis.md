# I296 — balanced King remainders: a counterexample and the exact-drift boundary

2026-10-13. **The proposed arbitrary-partner root-impurity bridge is false. Its arbitrary-partner exact-product-test-drift replacement is also false. The requested non-EB, all-n GAD stability theorem remains OPEN here. No acceptance or substantiality claim; current count 13/20 is unchanged.**

All OpenAI results at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. Entropy is in nats; trace norm is unhalved. The requested range is any compact interval inside (sqrt(2)-1,1). The counterexamples below actually work at every fixed 0<s<1. No numerical scans, subagents, live I294/I295 reads, shared-index edits, staging, commits or publication were used.

## 1. What the actual King proof supplies

Let A_s have Bloch matrix diag(s,s,s²), and put h_s=h((1+s)/2). For a pure input psi on a root qubit Q and a finite-dimensional tail, write r=Tr_tail Ppsi. King's actual quant-ph/0103156v2 Theorems 2–3, Lemma 4 and (49) supply a finite convex decomposition into phase-damping channels of parameter s, with input/output unitaries. Its input unitaries U_j satisfy

    Tr(Z U_j r U_j*)=0.

Equivalently, the rank-one projective measurements have axes v_j perpendicular to the Bloch vector of r. Both outcomes have probability 1/2. For pure psi their normalized tail inputs chi_j,+ and chi_j,- are pure, and each pair averages to the original tail marginal. With c_j>=0 and sum c_j=1, the old inequality is

    R(psi,Omega;E)
      := S((A_s tensor Omega)Ppsi)-h_s
           -sum_j c_j/2 [S(Omega Pchi_j,+)+S(Omega Pchi_j,-)]
      >=0.                                                     (1)

The SAME ensemble E is meant throughout. It can be chosen from r alone before Omega. We read the complete proof of Theorem 2 in Section 4, the complete convex/symmetry proof of Theorem 3 and Lemma 4 in Section 3, and Section 2 including the differentiation leading to (49). The proof first uses convexity on phase-damping branches, then the phase-damping/Epstein bound, then differentiates at p=1. Differentiating does not manufacture a strict loss. No original Epstein-paper read or quantitative Epstein stability theorem is asserted.

The pure-input restriction does not prevent a mixed state after the tail channel. That distinction is decisive below.

## 2. Exact two-qubit counterexample, valid for EVERY balanced ensemble

Fix 0<p<1 with p!=1/2, for example p=3/4. Let |+>,|-> denote the X eigenvectors and take

    psi = sqrt(p)|++> + sqrt(1-p)|-->.
    r = p P+ +(1-p) P- = (I+(2p-1)X)/2.

The root impurity is

    1-Tr(r²)=2p(1-p)>0.                                       (2)

Define the CPTP tail channel by recording the X-Schmidt label in orthogonal flags:

    Omega(T)=<+|T|+> |0><0| + <-|T|-> |1><1|.

Its Kraus operators are |0><+| and |1><-|. They satisfy sum K* K=I. It is an ordinary finite-dimensional qubit measurement channel.

For ANY balanced root measurement, its axis v obeys v_x=0, because 2p-1!=0. Thus each of its unit eigenvectors e_+,e_- obeys

    |<e_a,+>|²=|<e_a,->|²=1/2.

Both outcomes have probability 1/2. The normalized conditional tail has the form

    chi_a = sqrt(p) exp(i alpha_a)|+>
                  +sqrt(1-p) exp(i beta_a)|->.

Consequently, independently of the measurement axis, outcome and phase,

    Omega(Pchi_a)=beta := p|0><0|+(1-p)|1><1|,
    S(Omega(Pchi_a))=H(p).                                    (3)

On the other hand,

    (A_s tensor Omega)Ppsi
      =p sigma_+ tensor |0><0| +(1-p) sigma_- tensor |1><1|,
    sigma_±=(I±sX)/2,
    S(sigma_+)=S(sigma_-)=h_s.

The orthogonal flag blocks give exactly

    S((A_s tensor Omega)Ppsi)=H(p)+h_s.                        (4)

Equations (3)–(4) make R=0 for every possible balanced ensemble E, including every ensemble furnished by King. Hence

    R >= kappa_s(1-Tr r²), kappa_s>0

is impossible. At p=3/4 the allegedly paid impurity is 3/8. This is an exact analytic contradiction at tail dimension two, not a dimension-growing compactness objection. Allowing the balanced ensemble to depend on Omega would not repair it.

The unbalanced X measurement instead has probabilities p,1-p and pure flagged tail outputs. Its scalar remainder in this example is H(p). This shows the information that balance discards; it does NOT establish a universal entropy inequality for that unbalanced measurement.

## 3. Retaining BOTH old losses does not rescue the proposed bridge

This example also locates the failure in King's actual proof, rather than only at its final statement. Use any Lemma 4 channel decomposition

    A_s=sum_j c_j Gamma_Wj composed Psi_s composed Gamma_Uj,

and let O_Uj,O_Wj be its Bloch rotations. Its dephasing axis is perpendicular to X. Therefore O_Uj e_x is perpendicular to the dephasing Z axis, and the j-th branch maps the input X direction to

    s a_j,  a_j=O_Wj O_Uj e_x,  |a_j|=1.

Since A_s e_x=s e_x and all positive coefficients sum to one,

    sum_j c_j a_j=e_x.

Equality in the triangle inequality for unit vectors forces a_j=e_x for every positive-weight branch. More explicitly, sum c_j |a_j-e_x|²=0. After Omega, every branch output is therefore exactly the same flagged state in (4). The entropy concavity/Jensen loss is zero.

The dephased state for each input-rotated branch has two equal root blocks beta/2, so its entropy is log 2+H(p). The corresponding phase-damped output has entropy h_s+H(p). The phase-damping entropy bound is also exact. Thus BOTH the phase-damping slack and the mixture slack vanish while (2) stays positive. The maximally-entangled/identity-tail saturation in the parent brief was an important warning, but the present nonmaximal-Schmidt, label-recording example defeats the proposed tradeoff itself.

## 4. The exact nonnegative two-copy drift and the parent correction

Let

    T_n(psi)=2^(-n) sum_(S subset [n]) Tr((Ppsi)_S²),
    F_n=1-T_n.

The old Harrow–Montanaro mixed-state purity formula and I293's complete derivation give, for any pure-state ensemble of the tail marginal,

    delta_E(psi)
      :=F_n(psi)-sum_a q_a F_(n-1)(chi_a)
       =sum_a q_a T_(n-1)(chi_a)-T_n(psi)
      >=0.                                                    (5)

This is the exact quadratic variance drift. Its loose upper bound by root impurity is not an equality. It is already paid old material, not an I296 finding.

For the two-qubit example in Section 2, all conditional one-qubit tails are pure, so F_1=0. The root and tail marginals both have purity p²+(1-p)². Hence

    F_2=1-[1+Tr(r²)]/2=p(1-p),
    delta_E=p(1-p)>0.                                        (6)

Yet R=0. Therefore even

    R(psi,Omega;E)>=c_s delta_E(psi), c_s>0

is false for arbitrary CPTP Omega, for every balanced ensemble. The user/parent proposed investigating exact drift after the impurity counterexample, then explicitly corrected the arbitrary-partner version with this same two-qubit construction. We independently checked (6) and retain that correction. No arbitrary-partner exact-drift inequality is a premise.

Likewise, a faithful higher-copy productness test that has positive failure on this entangled input and zero failure on all pure one-site tails cannot be paid locally by this zero residual. Merely changing the copy number cannot solve this arbitrary-partner obstruction.

## 5. Actual GAD tensor tails still refute ROOT-IMPURITY payment

The arbitrary measurement partner could conceivably have been too permissive. In fact the impurity version also fails with actual GAD tensor powers, by an asymptotic version of the same construction.

For n>=2 set

    psi_(n,theta)=sqrt(p)|+>^tensor n
                         +exp(i theta)sqrt(1-p)|->^tensor n.

Its root marginal is the same r in Section 2. Every balanced root measurement produces pure (n-1)-site cats with exactly the same p and some phases. Let

    sigma_±=(I±sX)/2,
    beta_m=p sigma_+^tensor m +(1-p) sigma_-^tensor m,
    omega_(m,theta)=A_s^tensor m(Ppsi_(m,theta)).

The cross operator is

    C=A_s(|+><-|)=(s² Z-i s Y)/2,
    ||C||_1=s.

Indeed Tr(C*C)=(s²+s^4)/2 and det C=(s²-s^4)/4, so the two-by-two singular-value identity gives ||C||_1²=s². Consequently

    ||omega_(m,theta)-beta_m||_1
       <=2 sqrt(p(1-p)) s^m,                                (7)

uniformly in theta. I279's analytic cat/mixing mechanism is credited here; the sharper block analysis below avoids a dimension-dependent continuity estimate.

Let E_m be the classical conditional entropy of the binary component label L, of prior p, after m independent X measurements on beta_m. They are binary symmetric observations with crossover q=(1-s)/2. Then

    S(beta_m)=m h_s+H(p)-E_m.

The Bhattacharyya coefficient of the two one-site distributions is

    b_s=2 sqrt(q(1-q))=sqrt(1-s²)<1.

Shannon entropy is bounded by Renyi entropy of order 1/2, giving h(w)<=2 sqrt(w(1-w)). Summing this bound over observations yields

    0<=E_m<=2 sqrt(p(1-p)) b_s^m.                              (8)

Write C_(m,theta)=S(beta_m)-S(omega_(m,theta))>=0. Section 6 proves the dimension-free bound C_(m,theta)<=s^(2m). For any King ensemble at the root, with Omega=A_s^tensor m and n=m+1, exact cancellation gives

    R_(m+1)=E_m-E_(m+1)
            +sum_j c_j/2 [C_(m,theta_j,+)+C_(m,theta_j,-)]
            -C_(m+1,theta).                                  (9)

Thus

    0<=R_(m+1)<=2 sqrt(p(1-p)) b_s^m+s^(2m) ->0.              (10)

The fixed root impurity is 2p(1-p). This refutes every positive, n-independent root-impurity remainder even after restricting Omega to actual GAD tensor powers. The conclusion is uniform over ALL choices of balanced root ensembles, including n-dependent choices. It does not refute the global target: the cats' total output deficit tends to H(p)>0.

## 6. Exact blocks and the two analytic decay rates

This section investigates whether the same cats also obstruct the weaker exact-drift payment for GAD tensor tails. They do not. The distinction is quantitative, rather than inferred from a loose root-impurity bound.

Put a=(1+s)/2, q=(1-s)/2. In the X basis,

    C=s a |+><-| -s q |-><+|.

For a length-m X-basis string x with k minus signs, let

    u_x=a^(m-k) q^k, v_x=q^(m-k) a^k,
    d_x=p u_x+(1-p) v_x.

The state beta_m is diagonal with entries d_x. The cat output is a direct sum over complementary pairs {x,xbar} of the matrices

    [ d_x       z_x   ]
    [ z_x*    d_xbar  ],

where

    z_x=sqrt(p(1-p)) s^m
          [exp(-i theta)(-1)^k u_x
                     +exp(i theta)(-1)^(m-k) v_x].            (11)

Changing the convention for theta conjugates (11) and changes no conclusion. The block trace is w_x=u_x+v_x, and sum over complementary pairs w_x=1. Also

    d_x d_xbar
      =p(1-p)(u_x+v_x)²+(2p-1)²u_x v_x,
    |z_x|²<=p(1-p)s^(2m)(u_x+v_x)²
             <=s^(2m)d_x d_xbar.                             (12)

Since beta_m is the diagonal of omega_(m,theta),

    C_(m,theta)=D(omega_(m,theta)||beta_m).

For any full-rank sigma, scalar Jensen in eigenbases of rho,sigma gives

    D(rho||sigma)<=log Tr(rho² sigma^(-1)).

To verify the direction, use probability weights lambda_i |<i,j>|² and random variable lambda_i/mu_j. Its mean is Tr(rho² sigma^(-1)). Zero lambda_i contribute zero by continuity. Here (12) gives

    Tr(omega² beta^(-1))
       =1+sum_pairs |z_x|²(1/d_x+1/d_xbar)
       <=1+s^(2m).

Therefore, without any inverse-channel assertion,

    0<=C_(m,theta)<=log(1+s^(2m))<=s^(2m).                    (13)

For the precise leading term, divide each block by w_x. Its diagonal entry t_x=d_x/w_x lies in [min(p,1-p),max(p,1-p)], a fixed interval away from zero and one. The off-diagonal entry is s^m times a bounded coefficient. Taylor expansion of the TWO-BY-TWO block entropy, on that fixed interval, is uniform:

    entropy drop
       =s^(2m) |z_x/(s^m w_x)|² f(t_x)+O_p(s^(4m)),
    f(t)=[log t-log(1-t)]/(2t-1), f(1/2)=2.

After restoring the block weights and summing, the O term stays O_p(s^(4m)); there is no number-of-blocks factor. When u_x dominates v_x, or conversely, the quadratic coefficient approaches

    A_p=p(1-p) log(p/(1-p))/(2p-1)>0.                         (14)

Its difference from A_p is bounded by a p-dependent constant times min(u_x,v_x)/(u_x+v_x), uniformly in theta. This follows from the Lipschitz continuity of f on the fixed diagonal interval and expansion of the squared off-diagonal coefficient. Since

    sum_pairs min(u_x,v_x)
       <=(1/2) sum_all_x sqrt(u_x v_x)=(1/2)b_s^m,

we obtain the fully analytic, phase-uniform asymptotic

    C_(m,theta)
       =A_p s^(2m)+O_p(s^(2m)b_s^m+s^(4m)).                  (15)

For p=3/4, A_p=(3/8)log 3. Equation (15) uses a fixed-size scalar Taylor expansion with a summable block weight, not an n-uniform Taylor radius around an arbitrary product optimizer.

The other contribution in (9) is also positive and explicit:

    E_m-E_(m+1)=I(L;Y_(m+1)|Y^m)
      =sum_x d_x g_s(p u_x/d_x),
    g_s(t)=h(q+s t)-h(q).                                    (16)

The function g_s is strictly positive on (0,1), zero at the endpoints, and at most a constant depending on s times min(t,1-t), because q>0 and its derivative is bounded. Set ell=log(a/q)>0, j=k-m/2,

    D_j=p exp(-ell j)+(1-p)exp(ell j),
    W_j=p exp(-ell j)/D_j.

The exact sum in (16) is

    (a q)^(m/2) sum_(j in lattice, |j|<=m/2)
                   binom(m,m/2+j) D_j g_s(W_j).

The lattice is Z for even m and Z+1/2 for odd m. Its positive summand D_j g_s(W_j) is bounded by a constant times exp(-ell |j|). The elementary central-binomial bound is binom(m,k)<=C 2^m/sqrt(m), and for fixed j its ratio to 2^m sqrt(2/(pi m)) tends to one along the indicated parity. Dominated convergence therefore proves

    E_m-E_(m+1)
      ~sqrt(2/(pi m)) b_s^m B_parity(p,s),
    B_parity(p,s)=sum_(j in corresponding infinite lattice)
                         D_j g_s(W_j) in (0,infinity).         (17)

In particular it is Theta_(p,s)(b_s^m/sqrt(m)), with positive bounded parity constants. No numerical fit or saddle-point scan is used.

Substituting (15)–(17) into (9), uniformly over the SAME chosen King ensemble, gives

    R_(m+1)
      =[E_m-E_(m+1)] +A_p(1-s²)s^(2m)
         +O_p(s^(2m)b_s^m+s^(4m)).                            (18)

For u=s² and u_*=(sqrt(5)-1)/2, this means

    u<u_*: R_(m+1)=Theta_(p,s)(b_s^m/sqrt(m));
    u>=u_*: R_(m+1)~A_p(1-u)u^m.

At equality b_s=u, the coherence term dominates the ambiguity term by sqrt(m). These are two complementary mechanisms; omitting either one would give an incorrect rate screen.

## 7. Compare with the actual product-test drift

For an n-site cat, every nonempty proper reduced state has purity p²+(1-p)²; the empty and full reductions have purity one. The old purity formula directly gives

    F_n(psi_(n,theta))=2p(1-p)(1-2^(1-n)).

Every balanced root measurement for p!=1/2 gives (n-1)-site cats with the same p, so its exact drift, independent of the chosen phases and coefficients, is

    delta_E=2p(1-p)2^(1-n)=2p(1-p)2^(-m).                    (19)

This formula was supplied by the parent/user and independently checked. It explains why root impurity is an excessively large local charge on cats.

Crucially,

    max(s²,sqrt(1-s²)) >= (sqrt(5)-1)/2 >1/2.

From (18)–(19), for every fixed 0<s<1 and fixed p in (0,1) excluding 1/2,

    R_(m+1)/delta_E ->infinity,

uniformly over balanced root King ensembles. Thus these cats refute the tensor-tail root-impurity claim, but they do NOT refute tensor-tail exact-drift payment at channel-dependent exponential rates. Neither (18) nor this favorable comparison proves that payment for other inputs.

## 8. The exact remaining unpaid operation

A sufficient weaker bridge would be the following NEW estimate, restricted to actual tensor partners:

    For s in the requested compact interval, choose a rule E_s(r) for
    King ensembles from the root marginal alone, used in entropy and drift,
    such that for every n and every pure n-qubit psi,
    R(psi,A_s^tensor(n-1);E_s(r))>=c_s delta_E_s(r)(psi),
    c_s>0,                                                    (W)

with inf c_s>0 on that interval. This is a conjectural operation, NOT a theorem or premise. The arbitrary-CPTP-partner version is definitively excluded by Section 4. Section 7 removes one tempting counterexample to (W), not all counterexamples.

If (W) were proved, the identities

    D_n=R+sum_j c_j/2 [D_(n-1)(chi_j,+)+D_(n-1)(chi_j,-)],
    F_n=delta_E+sum_j c_j/2 [F_(n-1)(chi_j,+)+F_(n-1)(chi_j,-)]

would telescope on the same adaptive tree to D_n>=c_s F_n. The older Soleimanifar–Wright soundness gives closest-product infidelity epsilon<=3F_n. The already-paid pinned GAD amplitude estimate and I289 Hellinger rounding then give, conditionally,

    d_equatorial(psi)²
       <=[120/c_s+32/((1-s²)s²)]D_n.

This conditional calculation is included only to identify the exact missing operation. It is not a minor conditional bridge nominated as solved.

A genuinely amortized or block entropy-to-test estimate could replace (W). It would have to charge the one collective cat label once, and control the same global test or another test with independently established soundness. A channel-adapted higher-copy test would additionally need an entropy payment and global soundness proof. None is supplied.

Amosov Proposition 5 was reconstructed directly: for a balanced pure branch input, rho=(Psi_s tensor Id)Ppsi is supported on the two orthonormal root-conditioned vectors, and sigma is one half their support projection. Thus D(rho||sigma)=log 2-h_s. After Id tensor Omega, sigma becomes diag(Omega Pchi_+,Omega Pchi_-)/2, and the relative-entropy data-processing loss is exactly the phase-damping entropy remainder. This repairs the normalization issues in the served display for this specialization. The Section 2 counterexample has loss zero. Applying Proposition 5 to a mixed output of a preceding dephasing step without justification is still unpaid. The elementary complementary-dephasing serial/mixture identities in the parent note do not change that obstruction.

The alternative A_s=(1-s)D_s+s B_s has two components of minimum h_s, and the average partial symmetric-projector failure dominates (1-s)F_n. The missing entropy-to-partial-test estimate for heterogeneous branches is not obtained here. Selecting all D_s sites still loses (1-s)^n. I284 already excluded the non-CP same-s postprocessing map, and I279 excluded sums of original marginal impurities. No route revives either reduction.

## 9. Contribution, validation and limits

The concrete result is a verified analytic refutation of the precise balanced arbitrary-partner impurity bridge, including simultaneous saturation of both old losses; it also rules out arbitrary-partner local exact-drift payment and, by cats, tensor-partner impurity payment. The cat block calculation determines two phase-uniform residual rates and shows why this family does not obstruct the tensor-partner exact-drift replacement. These are route diagnostics, not the requested global non-EB theorem or an acceptance nomination. Their independent contribution assessment is left to the parent.

Credit: King for the actual balanced ensemble and additivity inequality; Amosov for the relative-entropy phase-damping formulation; Shor and frozen I289/I293 for the EB mechanism and its TECHNICAL classification; Harrow–Montanaro and Soleimanifar–Wright for the old test/purity/soundness tools; Bae et al. for depolarizing output-entropy stability precedent; pinned family 276 and I289 for the amplitude and rounding inputs; I279 for the cat-label obstruction mechanism; and the parent/user for proposing exact drift and correcting its arbitrary-partner version.

Validation is analytic: CPTP Kraus completeness; root balance for every permissible axis; exact flagged-output entropy; exact drift at n=2; equality of every positive-weight King branch; cross-operator singular values; complementary-pair blocks; positive block diagonals and uniform Taylor coefficients; summable block weights; the scalar Jensen relative-entropy bound; central-binomial/parity asymptotics; and comparison with (19). Frozen hashes match the three explicitly supplied digests. The authentication and reading log distinguish complete proof reads from source metadata and inherited paid results. Full external bodies were fetched and hashed only in memory, not written to disk.

The all-n non-EB target, (W), heterogeneous partial-test payment, and any channel-adapted higher-copy or amortized replacement remain unproved. No acceptance claim or count change.
