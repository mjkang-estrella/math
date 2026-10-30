# Independent full proof review of observed P3R draft

Myeongjin Kang; no affiliation. Original review prose CC BY 4.0; original review code MIT. Third-party source rights retained privately.

**Mathematical verdict: PASS_FULL_P3R for the exact observed candidate. No required repairs.** This is a mathematical reading review, not formal verification, a contribution verdict, terminal author-task integration, or authorization to count or publish. The campaign remains 5/10. The author task state is unknown; its completed handoff must be authenticated and compared with this reviewed object before any acceptance.

The unchanged candidate is `inputs/author/candidate.md`, SHA256 `b03e265c57e60a198f7d1d3a63ac807ff4c8587b3fede3b4ef9c8c9664dbc4f4`. The unchanged full scope is `inputs/author/original-scope.md`, SHA256 `0a2aeb8c581e421037ad7c87936c2016495d5babb974ab64be0fa15a16dd66f5`. Both parent-provided hashes were checked before reading their contents and before copying their original bytes. This verdict does not silently rebase to later author work. The preliminary parent reading and finite exact algebra controls were read as evidence, not adopted as an independent mathematical gate; their program was not run.

## Full scope retained

For every a>0, every 0<rho<1/2, every finite m>=3, and every realization in C^m of the two stated Grams, the proof establishes exactly three negative eigenvalues at every R>=0, exact unitary equivalence of corresponding one- and two-well subsystems, continuity of the entire negative-trace difference, negativity near R=0 and positivity for all sufficiently large R, and

    exp(4aR) Delta(R)/R^2 -> 64 a A^6 rho^3
                            =4096 a^4 rho^3/pi^3,
    A=sqrt(4a/pi).

These remain one result. There is no omission of a threshold eigenvalue, replacement by a chosen three-state trace, additional restriction on Gram realizations, or claim at rho=1/2. The explicit big-O expansion in candidate (1.3), which is stronger than the frozen limit, also follows.

## P1: object and source authentication

The observed draft is authenticated as above. A completed author package is not yet authenticated: the source task was reported `parent_not_active`, and no terminal handoff is inferred. The candidate refers to `operation-comparison.md`, which is absent in the observed author directory; that reference is not used as a mathematical premise. A contribution gate must review its own completed evidence.

All 14 source files in the observed author's `source-authentication.json` were copied unchanged, checked by SHA256, byte size and Git blob SHA1 against the complete 13,223-entry, nontruncated preprint catalogue, and independently compared byte-for-byte with raw GitHub URLs at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. `source-verification.json` records the results. A compact catalogue extract retains the relevant entries and identity of the complete catalogue; it is not a substitute for the independent pinned retrieval already performed.

The three actual `thm:main` statements were read in full, with their surrounding introductions. The equality companion assumes finite matrix dimension, 1/2<gamma<3/2, measurable Hermitian W>=0 and integral tr(W^(gamma+1/2))<infinity. Its optimizer is a constant-unitary direct sum of (r+1)a_j^2 sech^2(r a_j(x-x_j)), r=(gamma-1/2)^(-1), one negative eigenvalue per nonzero channel. At gamma=1, r=2 gives exactly 3a^2 sech^2(2ax). This classification applies to extremizers; it is not misapplied to the noncommuting three-well configurations. Both inequality companions sum all negative eigenvalues with multiplicity, possibly infinitely many before their bound, and do not state P3R.

The equality rigidity section was read entirely, including `rig:factorization` and `rig:partner`; its preliminaries and spectral-bound section were also read entirely. No new deduction is treated as stipulated source truth. In fact P3R's operative spectral and interaction arguments are independently reconstructed below; no equality classification is needed to infer the three-well count. Authentication of the other retained source files is not represented as reading their full proof bodies.

## P2: closed operators, entire negative spectrum and multiplicity

For candidate §2, q=b tanh(2ax) is real, bounded and has bounded derivative. Q=partial+q on H^1 is closed, since it is a bounded perturbation of the closed derivative. Its adjoint is -partial+q on H^1. Both Q*Q and QQ* have domain H^2: multiplication by q preserves H^1, and the condition partial f+qf in H^1 is equivalent to f in H^2. Thus the displayed differential expressions are identities of closed self-adjoint operators, not just identities on test functions. With nu=(sqrt(1+3lambda)-1)/2, 0<lambda<2 implies 0<nu<1; the partner correction 4a^2 nu(1-nu) sech^2 is nonnegative.

The L^2 kernel sech^nu is one-dimensional, gives energy -b^2, and Q*Q>=0 excludes lower energy. If h_lambda phi=E phi with -b^2<E<0, phi belongs to H^2 because its potential is bounded. Set mu=E+b^2>0. Then Q*Q phi=mu phi lies in Dom Q, so g=Qphi lies in Dom QQ*, is nonzero by ||g||^2=mu||phi||^2, and satisfies QQ*g=mu g. Since mu<b^2 this contradicts the partner lower bound. Decaying bounded potentials are relatively compact perturbations of the free operator; this also follows directly by local Rellich compactness and the vanishing tail of their multiplication operators. Consequently there is no other negative spectrum. The normalization integral in (2.3) gives the stated A exactly.

For §3, J is bounded, JJ*=W, and K=J*R0J is positive compact trace class at real k>0. Write C=(H0+k^2)^(-1/2)J. The form congruence of H+k^2 with I-CC* and equality of the nonzero spectra of CC* and C*C=K yield the strict counting identity, including multiplicities. This argument is valid even when J is not injective. The Gram inequality is a quadratic-form inequality: sandwich d I tensor R0 <= G tensor R0 <= c I tensor R0 by the diagonal sqrt(w_i) multiplication. Independent translations then identify the diagonal scalar blocks. There is no false pointwise ordering of the physical potential.

Since 0<d=1-2rho<c=1+2rho<2, each comparison scalar channel has exactly one negative eigenvalue. At every k>0 the upper bound gives N(H<-k^2)<=3. Four negative eigenvalues, however shallow, would violate this by taking k smaller than the square root of their least magnitude. The lower bound gives N(H<-k^2)>=3 for every k<b_d. It follows that exactly three negatives exist and all lie in [-b_c^2,-b_d^2]. This conclusion holds uniformly over R>=0. It supplies the essential protection against omitted shallow states.

For complex k in Re k>0, define R_a=(-partial^2+a^2)^(-1) and M(k) as the Fourier multiplier (p^2+a^2)/(p^2+k^2). On each compact subset of this half-plane M(k) is bounded and analytic in operator norm: its denominator has no real-p zero there and the local derivative bounds are uniform. Each sqrt(w_i) R_a^(1/2) is Hilbert–Schmidt, since its squared norm is proportional to integral w_i times integral dp/(p^2+a^2). Thus the weighted resolvent blocks factor as two fixed Hilbert–Schmidt operators with analytic bounded middle M(k), proving trace-norm analyticity. The same applies before separate translations and to K_e. Their Fredholm determinants are analytic.

If (I-K_e(k))f=0, psi=R0(k)J_e f is nonzero, belongs to H^2, and solves H_e psi=-k^2 psi. Conversely f=J_e*psi gives the inverse kernel correspondence. A vanishing J_e f would force f=0. Self-adjointness makes -k^2 real; with Re k>0, this forces Im k=0. Hence every determinant zero in the half-plane is positive real and physical. The scalar case gives the sole zero a.

At a positive zero k*, let P project orthogonally onto ker(I-K(k*)). On its complement Q, Q(I-K(k*))Q is invertible, since K(k*) is compact self-adjoint. The finite-dimensional Schur complement of I-K(k) on P is

    (k-k*) P(-K'(k*))P + O((k-k*)^2).

The derivative in candidate (5.7) is strictly negative definite on this kernel; hence the leading finite matrix is positive definite and invertible. Analytic invertible block factors reduce the Fredholm determinant to a nonvanishing analytic factor times the determinant of this Schur complement. Its zero has order dim P, exactly the physical multiplicity. This justifies the asserted conversion from derivative sign to zero order. Applied to the simple scalar eigenvalue it also proves that d0 has a simple zero at a and A has a simple pole. No unproved algebraic multiplicity assumption remains.

## P3: annular logarithm and full-trace contour

Factorization (5.4) follows from multiplication of I+trace-class operators wherever I-K0 is invertible; it is used on the contour, not at its central pole. The scalar analysis leaves A analytic and bounded on a neighborhood of C. Choose a fixed slightly thickened annulus around C with, for example, 0.89a<Re k<1.11a and with a excluded. The estimates of Lemma 6.1 hold there with adjusted constants, as does boundedness of A. For all sufficiently large R, ||T||op<1/2 throughout a possibly smaller such annulus.

The trace series in (5.5) therefore defines a single-valued analytic logarithm on that annulus. The first trace vanishes, and for ell>=2 the trace-ideal bound ||T||HS^2 ||T||op^(ell-2) gives locally uniform convergence. Finite-rank approximation, or the analytic Fredholm determinant identity, gives exp L=det(I-T); differentiating gives L'=(det(I-T))'/det(I-T). It is not necessary, and generally would be false, to extend this small-norm series through k=a. The candidate's specified single-valued contour branch is enough, and follows from its uniform norm bound by continuity on a neighborhood. This is an explicit justification of the existing argument, not a repaired hypothesis.

Along C the winding number of det(I-T) is zero because L returns to its initial value. Thus D and d0^3 have the same winding number, three. Both D and d0 are analytic inside the disk; by the argument principle D has three zeros counted by order there. P2 converts their orders to physical multiplicities. The global exactly-three count then ensures this disk contains the entire negative spectrum at large R, even though the earlier uniform enclosure (3.3) alone is much larger.

The sum of k_j^2 is S, since physical eigenvalues are -k_j^2. Subtracting the three local zeros gives (5.8), with its minus sign. Integration by parts is along a closed parametrized curve with the same initial and final value of L, so the boundary term vanishes. In particular no derivative estimate for the exponentially small remainder is needed: all subsequent estimates concern L itself on the fixed contour.

## P4: smooth complex tails, exact cancellation and coefficient

For d>0 the proposed rank-one kernel agrees exactly with B_d on s-t<=d. On z=s-t>d the modulus of their difference is bounded by 2 exp(b(z-d)), b=Re k. The squared kernel integral is controlled by the convolution of w with its translate. The bound w(x)<=12a^2 exp(-4a|x|), split into the three intervals in (6.2), yields C_a(1+z)exp(-4az). Thus the error square is at most

    C_a exp(-2bd) integral_d^infinity (1+z)exp(-(4a-2b)z) dz
       <=C_a(1+d)exp(-4ad),

uniformly on C. Since b<=1.1a<2a, both analytic vectors v_+ and v_- have uniformly bounded L^2 norms. The resulting HS and operator estimates are valid for the actual tails, without cutoffs. Bilinear rank-one notation has operator norm ||f||_2||g||_2 even at complex k, by Cauchy–Schwarz against the vector conjugate(g). Transpose is the bounded linear operation A^T=C A* C, with C complex conjugation; it reverses products and preserves trace. Hence B_ij^T=B_ji, K0^T=K0 and A^T=A at complex k. Cyclicity then equates each triangle with its reverse.

For each loopless closed walk on three vertices, each vertex has even incidence degree. Its three edge traversal counts therefore have a common parity. The common parity equals the parity of the total length. Flipping edge 13 preserves all even terms exactly and flips precisely the odd closed walks. There are six triangles; the factor -1/3 in the logarithm gives -2 z_e F_R, and subtraction gives -4rho^3 F_R. Higher changing lengths start at five, and summing (5.6) bounds their total uniformly by C exp(-5b0 R)=C exp(-4.5aR). This bound uses full operator traces rather than an approximate finite matrix walk.

For the triangle, replacing an adjacent kernel by its error costs sqrt(1+R)exp(-(2a+3b0)R), while replacing the long kernel costs sqrt(1+2R)exp(-(4a+2b0)R). The exponents are 4.7a and 5.8a, so their polynomial factors can be absorbed into exp(-4.5aR). A telescoping replacement uses exact or main-term kernels for the other factors; both obey the needed norm bounds. Two Hilbert–Schmidt factors and one bounded factor suffice for the product trace. The additional bounded A factors cause no difficulty.

The two forward blocks have main direction v_+ odot v_-, and the long return has v_- odot v_+. Their product trace is exactly the three pairings in (7.4), divided by (2k)^3, with the traveled exponential exp(-4kR). Replacing this by three identical mixed pairings would be incorrect, but the candidate retains the pure pairings in the correct positions. The vectors are analytic in L^2 on |Re k|<2a, so h is meromorphic throughout the disk, with only a pole of order at most three at a.

At a, eta=sqrt(w)phi satisfies K0 eta=eta. Differentiation gives <eta,K0'eta>=-2a, since R0(a)w phi=phi and ||phi||=1. The one-dimensional Schur calculation consequently gives

    Res_(k=a) A(k) = (eta odot eta)/(2a).

The residue is unchanged by the normalization of eta: normalization in the projection and in the eigenvalue derivative cancels. The bound-state resolvent formula, multiplied by exp(ax), admits dominated convergence; exp(ax-a|x-y|)<=exp(ay), and exp(ay)w(y)phi(y) is integrable. It gives both tail integrals 2aA, by evenness or the analogous left limit. Each of the three pairings in (7.4) has residue 2aA^2, and (2a)^(-3) times their product gives h_-3=A^6.

Write h=h_-3/(k-a)^3+h_-2/(k-a)^2+h_-1/(k-a)+regular. Direct coefficient extraction yields

    Res[k exp(-4kR)h(k)]
      = exp(-4aR) [8a h_-3 R^2
                  -4(h_-3+a h_-2)R+h_-2+a h_-1].

The contour trace formula contributes the positive factor 8rho^3, since its -2k is multiplied by -4rho^3. Therefore the leading coefficient is 64a A^6 rho^3, with positive sign. The uniform integrated error is O_(a,rho)(exp(-4.5aR)); after factoring exp(-4aR) it is absorbed into O_(a,rho)(R+1). The exact requested constant is 4096a^4rho^3/pi^3. There is no unresolved sign, exponent, normalization or trace-ideal error here.

## Remaining clauses and conclusion

The Gram eigenvalues are positive and less than two for the full open rho interval. Every Gram realization has a three-dimensional active span; the Gram-preserving isometry extends to a constant unitary in C^m. The one- and two-well projection equivalence uses only absolute pair overlaps and is exact at every separation. For continuity, the sum of the shift coefficients is 0+1+2=3, giving candidate (4.1); bounded-perturbation min–max then gives the eigenvalue Lipschitz bound. Because precisely three eigenvalues stay negative, their entire negative trace is continuous.

At R=0 diagonalizing the Gram gives (4.2). Direct differentiation gives f'''=-(81/4)(1+3lambda)^(-5/2). Integrating the centered second difference of F' over [-rho,rho] gives exactly (4.2), and its strict negativity follows from strict concavity of F' over all tested arguments. Hence Delta(0)<0, continuity gives the required nonempty interval including R=0, and the positive asymptotic gives positivity for every sufficiently large R. All quantifiers of the frozen target are paid.

## P5: contribution is a separate gate

This proof review does not assign SUBSTANTIAL, TECHNICAL or DUPLICATE. The scalar supersymmetric factorization, Gram comparison, analytic Fredholm determinant, logarithmic loop expansion, Bargmann triangle phase, and residue extraction are established operations or short deductions; the proof itself acknowledges those antecedents. The mathematical feature checked here is their combined use for a full continuum trace, exact pair equivalence, an all-R count and reversal with an explicit limit. Those clauses must remain one proposed result. A contribution reviewer must compare that combination with actual multiple-scattering and phase-ordering primary bodies; absence of an exact hit and a new constant do not establish substantial novelty. No worldwide-priority claim follows from this gate.

No repair was used to obtain PASS_FULL_P3R. Optional expository improvements are to state Dom Q=H^1 explicitly, give the finite-dimensional Schur multiplicity argument, and say “analytic on an annular neighborhood of C” when introducing L. These merely spell out consequences of the existing hypotheses and estimates. The later final author handoff still needs reconciliation against the two exact reviewed hashes before parent acceptance.

During this review the live author directory changed: the original top-level candidate and scope paths disappeared and a `screened-out-p3r/` directory appeared. This is an external author-state change, not a change to the exact retained proof or a mathematical counterexample. No later author content was substituted into this review. The after-receipt records the discrepancy; it cannot honestly certify unchanged live source paths. The internal reviewed inputs remain byte-for-byte fixed and the parent was informed promptly.
