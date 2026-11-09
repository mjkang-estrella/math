# P3R: reversal of three-channel phase ordering for smooth optimizer wells

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Third-party rights retained privately. Research proof candidate, not a manuscript or independent certificate. **counted=false**. The full frozen target is original-scope.md; no clause is replaced below.

## 1. Statement and source boundary

Let a>0, 0<rho<1/2 and m>=3 finite. Choose triples of unit vectors in C^m with Gram matrices

    G+ = [[1,rho,rho],[rho,1,rho],[rho,rho,1]],
    G- = [[1,rho,-rho],[rho,1,rho],[-rho,rho,1]].

Such triples exist: these real symmetric matrices have eigenvalues

    spec G+ = {1+2rho,1-rho,1-rho},
    spec G- = {1-2rho,1+rho,1+rho},                         (1.1)

and so are positive definite; take the columns of their positive square roots and add zero coordinates. Write P_i^e=u_i^e(u_i^e)* and

    w(x)=3a^2 sech^2(2ax),
    W_e,R(x)=sum_i w(x-(i-1)R) P_i^e,
    H_e(R)=-d^2/dx^2-W_e,R,
    S_e(R)=Tr(H_e(R))_- .                                (1.2)

Here the last trace is the sum of the absolute values of **all** negative eigenvalues. We claim:

**Theorem P3R.** Each operator in (1.2) has exactly three negative eigenvalues for every R>=0. Every corresponding one- or two-well subsystem of the two models is unitarily equivalent. Their full trace difference Delta(R)=S_+(R)-S_-(R) is continuous, negative for all sufficiently small R>=0, positive for every sufficiently large R, and

    Delta(R) = [64 a A^6 rho^3 R^2 + O_(a,rho)(R+1)] e^(-4aR),
    A=sqrt(4a/pi).                                      (1.3)

In particular its normalized limit is 4096 a^4 rho^3/pi^3 as frozen. Constants do not depend on the representation of the Gram matrices or inactive channels.

The source family is 262 at openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its equality companion, `thm:main` and `rig:factorization`–`rig:partner`, supplies the optimizer shape and its one-bound-state interpretation at gamma=1. Both inequality companions' `thm:main` statements include the full negative spectrum and the sharp constant. We accept those source theorems, but **none of them states P3R**. For clarity the local factorizations used here are independently calculated in §2. No new sharp constant is asserted and no source theorem's truth is audited.

The proof's new work is the full-spectrum Gram bracket, the exact cancellation under phase switching, and extracting the triangle through actual overlapping sech tails on a spectral contour. Determinants, Birman–Schwinger reduction, multiple-scattering expansions and the three-vertex Bargmann invariant are established operations; operation-comparison.md separates them from the proposed combined result.

## 2. Local spectral calculation, including scaled wells

For lambda in (0,2), set

    nu=(sqrt(1+3lambda)-1)/2,     b=2a nu,
    q(x)=b tanh(2ax),            Q=partial_x+q.

Then 0<nu<1 and 4nu(nu+1)=3lambda. Direct differentiation on H^2(R) gives

    Q*Q = -partial_x^2 - lambda w + b^2,
    QQ* = -partial_x^2 + b^2 + 4a^2 nu(1-nu) sech^2(2ax) >= b^2.  (2.1)

The kernel of Q is spanned by sech^nu(2ax), an L^2 function, so -b^2 is a simple eigenvalue of h_lambda=-partial_x^2-lambda w. There is no lower eigenvalue by the first identity. If -b^2<E<0 were another eigenvalue, Q would map its eigenfunction to a nonzero eigenfunction of QQ* with eigenvalue E+b^2 in (0,b^2), contradicting the second identity. The potential is bounded and decays exponentially, so its negative spectrum is discrete; (2.1) proves that it consists of just this one eigenvalue. Consequently

    Tr(h_lambda)_- = a^2 f(lambda),
    f(lambda)=(sqrt(1+3lambda)-1)^2.                       (2.2)

At lambda=1, nu=1/2, b=a, and the normalized eigenfunction is

    phi(x)=sqrt(2a/pi) sech^(1/2)(2ax),
    phi(x)=A e^(-a|x|)(1+o(1)),   A=sqrt(4a/pi).           (2.3)

Normalization follows from integral_R sech(2ax) dx=pi/(2a). All signs and normalizations in the interaction calculation below refer to (2.3).

## 3. Lifted Birman–Schwinger bracket and the entire negative spectrum

Let R0(k)=(-partial_x^2+k^2)^(-1), k>0. Its kernel is e^(-k|x-y|)/(2k). Put w_i(x)=w(x-(i-1)R). On the auxiliary space K=direct_sum_(i=1)^3 L^2(R), define

    (J_e f)(x)=sum_i u_i^e sqrt(w_i(x)) f_i(x).

Then J_e J_e*=W_e,R as a multiplication operator. The lifted Birman–Schwinger operator is

    K_e(k)=J_e* (R0(k) tensor I_m) J_e,
    (K_e(k))_ij = g_ij^e sqrt(w_i) R0(k) sqrt(w_j).        (3.1)

It is compact, positive, and trace class. The number of eigenvalues of H_e(R) below -k^2, counted with multiplicity, equals the number of eigenvalues of K_e(k) greater than one. This follows by writing H_e(R)+k^2=H0+k^2-J_e J_e* and applying the variational principle to (H0+k^2)^(-1/2)J_e; the nonzero spectra of its two products coincide.

Set d=1-2rho>0 and c=1+2rho<2. Both Gram matrices satisfy d I_3<=G_e<=c I_3. Since R0(k)>=0,

    d diag_i(sqrt(w_i) R0(k) sqrt(w_i))
       <= K_e(k)
       <= c diag_i(sqrt(w_i) R0(k) sqrt(w_i)).             (3.2)

For precision, this comparison is first made on L^2(R;C^3): G_e tensor R0(k) lies between d I_3 tensor R0(k) and c I_3 tensor R0(k). Conjugate by diag_i sqrt(w_i). Translating each auxiliary coordinate separately then makes all three diagonal blocks identical. No pointwise ordering of W_e,R by a scalar three-well potential is being asserted.

The upper comparison counts at most three eigenvalues greater than one for every k>0, because each of the three scalar potentials c w_i has exactly one negative eigenvalue by §2. Thus H_e(R) has at most three negative eigenvalues in total. For every k<b_d=a(sqrt(1+3d)-1), the lower comparison has exactly three eigenvalues greater than one. Therefore H_e(R) has at least three eigenvalues below -k^2. It follows that it has exactly three negative eigenvalues, all bounded away from zero uniformly in R. The same comparison at c bounds their magnitudes above by b_c^2. In particular

    -b_c^2 <= lambda_j(H_e(R)) <= -b_d^2 <0,  j=1,2,3.    (3.3)

This proves the full-spectrum clause for **every** R>=0 and excludes any uncounted shallow states. The free orthogonal complement of span{u_i^e} contributes none.

## 4. Pair equivalence, continuity, and the coalesced sign

For a single vector, its rank-one projection is unitarily equivalent to any other. For two unit vectors, the absolute value of their inner product determines the ordered pair of rank-one projections up to a common unitary: choose phases to make the inner product the same nonnegative real number, map one two-dimensional Gram realization isometrically to the other, and extend to a unitary on C^m. Every pair in our two triples has overlap magnitude rho. The same constant unitary therefore conjugates the entire corresponding two-well potential at all x and all R. This proves the exact subsystem claim.

The potential W_e,R changes continuously in operator L^infinity norm with R. Indeed

    ||W_e,R-W_e,R'||_infinity <= 3||w'||_infinity |R-R'|.  (4.1)

The bounded-perturbation variational principle gives the same Lipschitz bound for each ordered eigenvalue. By §3 exactly three are negative, so S_e and Delta are continuous (in fact Lipschitz).

At R=0, the nonzero eigenvalues of sum_i P_i^e are the eigenvalues of G_e, and its complement is zero. Thus (1.1) and (2.2) give

    Delta(0)/a^2 = f(1+2rho)+2 f(1-rho)
                         -f(1-2rho)-2 f(1+rho).          (4.2)

All six arguments lie in (0,2). Direct differentiation gives

    f'''(lambda)=-(81/4)(1+3lambda)^(-5/2)<0.             (4.3)

Put F(t)=f(1+t). The right-hand side of (4.2) equals

    integral_(-rho)^rho [F'(t+rho)+F'(t-rho)-2F'(t)] dt.  (4.4)

Because F' is strictly concave on (-1,1), the integrand is strictly negative throughout the integration interval. Thus Delta(0)<0. Continuity gives the asserted negative interval. The rest of the proof establishes the large-distance sign without a finite-dimensional trial-state substitution.

## 5. Analytic determinants and a fixed contour

We now work with complex k with Re k>0 and, specifically, on and inside

    C={k: |k-a|=a/10}, oriented counterclockwise.          (5.1)

Write b0=9a/10. Use separate translations of the three auxiliary coordinates in (3.1). On L^2(R), let

    K0(k)(s,t)=sqrt(w(s)) e^(-k|s-t|)/(2k) sqrt(w(t)),
    B_ij(k)(s,t)=sqrt(w(s))
           e^(-k|s-t+(i-j)R|)/(2k) sqrt(w(t)).           (5.2)

The diagonal blocks are K0 and the off-diagonal blocks are g_ij^e B_ij. Set

    A(k)=(I-K0(k))^(-1),
    T_e(k)_ii=0,     T_e(k)_ij=g_ij^e A(k)B_ij(k).        (5.3)

These operators are analytic trace-class families before inversion, and A is meromorphic. One direct trace-class justification is to factor each weighted resolvent through (-partial_x^2+a^2)^(-1/2): multiplication by sqrt(w_i) followed by that inverse square root is Hilbert–Schmidt since w_i is integrable and integral(dp)/(p^2+a^2)<infinity. The middle multiplier (p^2+a^2)/(p^2+k^2) is bounded locally uniformly on Re k>0. Products of two Hilbert–Schmidt operators are trace class. The explicit kernels also show Hilbert–Schmidt analyticity and the same factorization gives trace-norm analyticity.

The zeros of d0(k)=det(I-K0(k)) in Re k>0 are precisely positive k with -k^2 a negative eigenvalue of the local scalar operator. Self-adjointness excludes nonreal zeros there. By §2 the only zero is at a, and it is simple. We verify its nonzero derivative and the inverse residue in §8. Thus A is bounded on C.

The exact Fredholm factorization is

    D_e(k):=det(I-K_e(k))
         = d0(k)^3 det(I-T_e(k)).                       (5.4)

Indeed I-K_e=diag(I-K0) (I-T_e) wherever the first factor is invertible, and determinants multiply. All statements on C concern invertible first factors.

Lemma 6.1 below gives ||T_e||_HS+||T_e||_op<=C_(a,rho) e^(-b0 R) uniformly on C. For R large this is less than 1/2. Hence

    L_e(k)=log det(I-T_e(k))
          =-sum_(ell>=1) Tr(T_e(k)^ell)/ell             (5.5)

is given by a uniformly convergent series on C. The first trace is zero because all diagonal blocks vanish. For ell>=2 use

    |Tr T^ell| <= ||T||_HS^2 ||T||_op^(ell-2).           (5.6)

This also proves uniform convergence of the terms we later integrate. The branch in (5.5) is a single-valued continuous logarithm around C, so its integral derivative has winding number zero.

The argument principle in (5.4) now shows that D_e has three zeros inside C, with orders counted, as d0^3 does. For a real positive zero k*, the order of D_e equals the physical eigenvalue multiplicity. This familiar multiplicity assertion can be checked directly: on ker(I-K_e(k*)),

    <f,K_e'(k*)f> = -2k* ||R0(k*)J_e f||^2 <0           (5.7)

for nonzero f. Its restriction is negative definite because a vector in that kernel with J_e f=0 would vanish. Thus all kernel crossings are first order, with total order equal to their dimension. The kernel itself is isomorphic to the physical eigenspace. All zeros in the disk must be positive real, again by self-adjointness. Since there are exactly three negative eigenvalues globally by §3, these three zeros account for the **entire** trace for large R.

Consequently the argument principle and integration by parts give

    S_e(R)-3a^2
       = (1/(2pi i)) integral_C k^2 (D_e'/D_e-3d0'/d0) dk
       = -(1/(2pi i)) integral_C 2k L_e(k) dk.           (5.8)

Integration by parts is legitimate along the closed contour because (5.5) returns to its initial value. We use the sign in (5.8) throughout.

## 6. Actual smooth-tail estimate

**Lemma 6.1.** For d>0, let B_d have kernel

    sqrt(w(s)) e^(-k|s-t-d|)/(2k) sqrt(w(t)).

Define v_+(k,s)=sqrt(w(s))e^(ks), v_-(k,s)=sqrt(w(s))e^(-ks), and use the bilinear rank-one notation

    (f odot g)h = f integral_R g(t)h(t) dt.

There is no complex conjugation in this analytic notation. Its operator and Hilbert–Schmidt norms are ||f||_2||g||_2. Uniformly for k on C,

    B_d = e^(-kd)/(2k) v_+ odot v_- + E_d,
    ||E_d||_HS <= C_a sqrt(1+d) e^(-2ad),
    ||B_d||_HS <= C_a e^(-(Re k)d).                     (6.1)

The reverse-direction block is the transpose, with v_+ and v_- exchanged.

**Proof.** The identity of kernels is exact on s-t<=d. Put b=Re k, so 0.9a<=b<=1.1a. On s-t>d, the difference of the two exponentials is bounded in modulus by 2e^(b(s-t-d)). Also

    w(x)<=12a^2 e^(-4a|x|),
    integral_R w(y+z)w(y)dy <= C_a (1+z)e^(-4az), z>=0. (6.2)

The latter follows by splitting y into (-infinity,-z), [-z,0], and (0,infinity). Squaring the error kernel and setting z=s-t therefore yields

    ||E_d||_HS^2
      <= C_a integral_d^infinity (1+z)e^(-4az+2b(z-d)) dz
      <= C_a (1+d)e^(-4ad),                            (6.3)

uniformly since 4a-2b>=1.8a. The vectors v_+ and v_- have uniformly bounded L^2 norms because 2|Re k|<4a. The rank-one main term has norm at most C_a e^(-bd), and sqrt(1+d)e^(-2ad)<=C_a e^(-bd). This proves (6.1). Transposition proves the last assertion. No compact cutoff of the wells has been inserted. QED.

For our blocks d is R or 2R. Lemma 6.1 and boundedness of A on C give the smallness estimate used in §5.

## 7. Phase cancellation and isolation of the triangle

In a term of Tr(T_e^ell), write the channel indices as a closed walk of length ell on {1,2,3}; consecutive indices differ because T_ii=0. The coefficient of its scalar operator trace is the product of the corresponding g_ij. In G- only the edge 13 has changed sign.

For any closed walk, the parities of its numbers of traversals of 12, 23 and 13 are equal: at each vertex the sum of its incident traversal counts is even. Therefore a walk changes sign precisely when all three edge counts are odd. Its length must then be odd. This proves exact cancellation of the **entire even part** of (5.5) between + and -, with no approximation to any block.

There are no length-one contributions, and the first changing walks are the six length-three oriented triangles. By cyclicity of the trace their three choices of starting vertex have equal traces. Reversing a triangle also gives the same trace because K0(k), A(k), and the B_ij(k) are symmetric under the appropriate kernel transpose, B_ij^T=B_ji, and trace is invariant under transpose. All these assertions are bilinear transpose assertions at complex k, not conjugation identities. They are valid first for finite-rank kernel approximations and then by Hilbert–Schmidt/trace-norm convergence.

Put

    F_R(k)=Tr(A B12 A B23 A B31).                       (7.1)

The cubic part of L_e is -2 z_e F_R, with

    z_+=rho^3,       z_-=-rho^3.

Every remaining changing walk has length at least five. By (5.6), uniformly on C its total contribution is O_(a,rho)(e^(-5b0 R)). Thus the exact difference is

    L_+(k)-L_-(k) = -4rho^3 F_R(k)
                           + O_(a,rho)(e^(-9aR/2)).     (7.2)

We next replace only the three cross-well kernels in (7.1) by the rank-one terms of Lemma 6.1. If an adjacent block is replaced by its error, the product trace is bounded by

    C_a sqrt(1+R) e^(-(2a+3b0)R)
       =C_a sqrt(1+R)e^(-4.7aR).                       (7.3)

Here the other adjacent block costs e^(-b0 R) and the long block e^(-2b0 R). If the long block is the error, the bound is C_a sqrt(1+2R)e^(-(4a+2b0)R). The same bounds hold in the three-term telescoping difference because both exact and rank-one blocks have the norm estimates in Lemma 6.1. Use |Tr XYZ|<=||X||_HS||Y||_HS||Z||_op and absorb the bounded A factors. These errors are O_a(e^(-9aR/2)).

Define the analytic bilinear pairing [f,g]=integral f g and

    h(k) = (2k)^(-3)
       [v_-,A v_+] [v_-,A v_-] [v_+,A v_+].            (7.4)

Multiplying the rank-one operators in their cyclic order now gives

    F_R(k)=e^(-4kR)h(k)+O_a(e^(-9aR/2))               (7.5)

on C. The traveled distance is R+R+2R=4R. The function h is meromorphic inside C, independent of R, and has a pole of order at most three at a and no other singularity there. Equations (7.2)–(7.5) isolate the target-scale interaction of the **actual smooth full operator**. Higher loops and overlapping tails have errors smaller than e^(-4aR), so cannot alter the coefficient in (1.3).

## 8. Local inverse residue and the coefficient

Let eta=sqrt(w)phi, with phi from (2.3), and use real L^2 pairings at k=a. Then K0(a)eta=eta. Differentiating R0(k) gives

    <eta,K0'(a)eta>
      =-2a ||R0(a)sqrt(w)eta||_2^2
      =-2a ||phi||_2^2=-2a.                            (8.1)

The eigenvalue one of K0(a) is simple, since its kernel equation is equivalent to the simple local bound-state equation. Analytic inversion across this one-dimensional kernel, or a one-dimensional Schur complement with its invertible orthogonal complement, gives

    A(k) = (eta odot eta)/(2a(k-a)) + A_reg(k),          (8.2)

where A_reg is bounded analytic near a. To check the normalization directly, divide eta by its norm; the derivative of the corresponding eigenvalue of K0 is -2a/||eta||^2, and the projection coefficient in the inverse is therefore precisely (eta odot eta)/(2a).

The resolvent representation of the bound state reads

    phi(x)=integral_R e^(-a|x-y|)/(2a) w(y)phi(y)dy.

The exponential decay of w phi permits multiplication by e^(ax) and passage to x->+infinity, and similarly to -infinity. Formula (2.3) consequently yields

    integral_R e^(ay)w(y)phi(y)dy
      =integral_R e^(-ay)w(y)phi(y)dy=2a A.             (8.3)

Thus each of the three factors [v_sign,A v_sign'] in (7.4) has residue

    (2a A)^2/(2a)=2a A^2.

The analytic factors v_sign(k) are evaluated at a for this coefficient. It follows that

    lim_(k->a) (k-a)^3 h(k)=A^6.                       (8.4)

No unknown one-well scattering constant remains in this leading coefficient.

## 9. Full trace asymptotic and sign reversal

Subtract (5.8) for the two models, insert (7.2)–(7.5), and integrate the uniform errors on the fixed contour. The result is

    Delta(R) = 8rho^3 Res_(k=a) [k e^(-4kR)h(k)]
                                      +O_(a,rho)(e^(-9aR/2)).    (9.1)

Since h has a pole of order at most three and its coefficient of (k-a)^(-3) is A^6, the residue is e^(-4aR) times a polynomial of degree two in R. The R^2 coefficient comes solely from the quadratic term in e^(-4(k-a)R), namely 8R^2(k-a)^2, multiplied by a A^6/(k-a)^3. Hence

    Res_(k=a) [k e^(-4kR)h(k)]
       =e^(-4aR)[8a A^6 R^2+O_a(R+1)].                (9.2)

Combining (9.1) and (9.2) proves (1.3), and

    64a A^6 rho^3 = 64a (4a/pi)^3 rho^3
                         =4096 a^4 rho^3/pi^3 >0.

Thus Delta(R)>0 for every sufficiently large R. Section 4 gives Delta(R)<0 for all sufficiently small R>=0 and continuity on the full half-line. In particular there is at least one crossing; no uniqueness is claimed. This completes every clause of the original scope.

## 10. What the proof does and does not establish

This is an author-level proposed full proof of P3R, not an independent PASS. All a>0, 0<rho<1/2, m>=3 and Gram realizations remain included. Every subsystem equality is exact; the full trace is not a selected three-state approximation. At large R the three-state pole is used only through a contour that contains the entire negative spectrum, proved by the separate Gram bracket. The first phase-sensitive trace survives at order R^2 e^(-4aR), although the leading individual tunnelling splittings occur at larger scales.

The construction is tied to the gamma=1 optimizer shape. This exact choice was frozen at the outset; no broader failed target has been replaced. The upper and lower Gram bounds, factorization, Fredholm reduction, loop expansion, and geometric phase all have standard antecedents. The proposed result combines them to give an all-pair-identical reversal for a full continuum spectral observable. Whether that combination meets the campaign's substantial-contribution threshold remains an independent gate. No assertion of worldwide novelty, count, publication, submission, manuscript readiness or formal verification follows from this proof write-up.
