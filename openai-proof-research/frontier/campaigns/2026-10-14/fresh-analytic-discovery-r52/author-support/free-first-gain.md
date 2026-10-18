# Broadened jets: a first-collision mass estimate

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Status: parent author calculation, not an independent review, a nonlinear closure, or a campaign nominee. This addresses the single-packet first-gain test in analytic r52. No target is frozen or weakened here. All constants below can depend on fixed positive alpha, gamma, K and the fixed smooth compactly supported velocity density J, but not on s, d, or t. The prototype is on R^3 before periodicization.

## Kernel and a local smoothing bound

Use the three-dimensional hard-sphere gain with ordinary sphere area measure. Its incoming-pair law, as in the pinned September source, Section 3, Lemma `lem:carleman`, is

    integral psi(v) P(c,c)(v) dv
      = integral c(p)c(q) (|p-q|/2)
          integral_{S^2} psi((p+q)/2+|p-q|omega/2) d omega dp dq.

Let G_d(w)=(pi d^2)^(-1) exp(-|w|^2/d^2) on R^2. If

    c = rho G_d tensor nu,

where nu is any axial probability measure, then P(c,c) has a Lebesgue density bounded by 4 rho^2/d^2. Indeed, condition on the two axial coordinates. The transverse center M=(pbar+qbar)/2 is independent of the transverse relative vector and has density bounded by 2/(pi d^2). Given the relative vector of length r, write sphere area as d phi d omega_3. The change from omega_3 to outgoing v_3 has derivative r/2, cancelling the factor r/2 in the collision law. The transverse center density is then bounded by its supremum, and integration over phi gives 2pi. Integrating the remaining probability laws proves the claim. The zero-relative-vector set contributes zero and does not create an atom.

If additionally nu is supported in [V-Dd,V+Dd], for fixed D, then

    P(c,c)(v) <= C_D rho^2 d^(-2)
                    exp(-|v-V e_3|^2/(2d^2)).                 (1)

For a proof, energy conservation about V gives

    |pbar|^2+|qbar|^2 >= |v-V e_3|^2-2D^2 d^2.

Split half the transverse Gaussian exponent off the product. The remaining transverse laws are G_{sqrt(2)d}, each with multiplicative factor 2. Apply the preceding bound at width sqrt(2)d. For example C_D=8 exp(D^2) suffices. This reasoning applies also to singular axial laws; no bound on an axial density is used.

## Exact free packet and an enlarged derivative profile

Fix sigma in {+1,-1} and put

    a(z)=sigma+alpha tanh(gamma z/s),
    lambda_0(z)=a'(z)=(alpha gamma/s) sech^2(gamma z/s).

Let U(u,z)=a(z-u U(u,z)) and lambda(u,z)=U_z(u,z). Thus, if tau+u a(tau)=z,

    lambda(u,z)=lambda_0(tau)/(1+u lambda_0(tau)).

The function lambda(u,.) is even and decreasing away from z=sigma u. Its maximum is

    L_u = 1/(s/(alpha gamma)+u).

Take exactly the source-shaped datum with arbitrary transverse mask E,

    c^0(x,v)=1_E(y) 1_{|z|<1/8} (K/s) sech^2(gamma z/s)
                 d^(-3) J((v-a(z)e_3)/d),

where J is supported in the unit ball, and let f(u,x,v)=c^0(x-uv,v).

In the change of variables vbar=d wbar and

    p=a(z-u p)+d w,

the axial coefficient in f dv is exactly

    [K/(alpha gamma)] lambda(u,z-u d w).

This follows by differentiating the implicit equation; its Jacobian is d/(1+u a'(z-u p)). The axial spatial cutoff and transverse mask can be dropped for an upper bound. Since J(wbar,w) <= C exp(-|wbar|^2) 1_{|w|<=1}, f is dominated, as a velocity measure, by

    C K Lambda(u,z) G_d tensor nu_{u,z},

where nu_{u,z} is the pushforward of the uniform probability on [-1,1] under w -> p, and

    Lambda(u,z)=sup_{|delta|<=u d} lambda(u,z-delta).

The monotonicity of p -> p-a(z-u p) shows |p-U(u,z)|<=d. Thus nu is supported in [U-d,U+d].

Define a second center by

    V(u,z)=sigma+integral_{sigma u}^z Lambda(u,r) dr.

Then V_z=Lambda<=L_u and |V-U|<=u d L_u<=d. To see the latter, on the positive half-line about sigma u the enlarged derivative has a plateau of length u d at height L_u and then is a translate of the original derivative. Its excess integral up to any point lies between zero and u d L_u. The negative half-line is symmetric. In particular nu lies in [V-2d,V+2d]. Applying (1) yields

    P(f,f)(u,x,v) <= C K^2 d^(-2) Lambda(u,z)^2
                        exp(-|v-V(u,z)e_3|^2/(2d^2)).         (2)

This is an upper bound for the actual compactly supported free packet, not just for a linear-drift Gaussian. It is not an upper bound for a nonlinear solution.

## Integration along free paths

Set

    G(t,x,v)=integral_0^t P(f,f)(u,x-(t-u)v,v) du.

For fixed u,t,z let T=t-u and make the axial substitution

    r=v_3-V(u,z-T v_3).

The function V(u,.) is bounded (its deviation from the bounded U is at most d), so this is an onto increasing change of variables. Its derivative is 1+T Lambda(u,z-Tv_3). Since l -> l^2/(1+T l) is increasing for l>=0,

    Lambda^2/(1+T Lambda)
       <= L_u^2/(1+T L_u)
       = 1/[(s/(alpha gamma)+u)(s/(alpha gamma)+t)].

The transverse and axial Gaussian integrals in (2) therefore give

    integral P(f,f)(u,x-(t-u)v,v) dv
       <= C K^2 d/[(s/(alpha gamma)+u)(s/(alpha gamma)+t)].

Tonelli and integration in u prove

    integral G(t,x,v) dv
       <= C K^2 d log(1+alpha gamma t/s)/(s/(alpha gamma)+t)
       <= C' K^2 d log(1+t/s)/(s+t).                         (3)

This holds uniformly in x and t>=0 for a single unperiodized packet. Spatial mask removal in (2) does not discard the following exact support fact: the actual free input has transverse position within u d of E and velocities within Euclidean distance d of U e_3. Energy conservation about U implies each outgoing velocity has norm relative to U e_3 at most sqrt(2)d. Hence G vanishes unless dist(y,E)<=sqrt(2) t d. The Gaussian estimate itself is an upper bound, not a claim that the actual first gain has Gaussian tails outside this compact velocity support at its collision time.

## Limits and source reads

This proves only the proposed first-iterate velocity-mass estimate and transverse localization. It does not control P(f,G), P(G,G), interactions between distinct scales, repeated velocity broadening, or a norm preserved under the nonlinear gain. It does not prove the required flat spontaneous hot source, global continuation, two distinct entropy solutions, or the proposed L^2 initial-data target. Periodic copies and same-sign cross-scale collisions have not been included in (3). The fact that a fixed time interval meets finitely many lattice copies alone does not control collisions between them.

Parent actual reads for this calculation: the full September `03-kernel.tex` and its `04-jets.tex` lines 1–220; October `05-cold.tex` lines 1–220; r52 `working-interface.md` in full. Source bodies reside in the ignored private source tree of analytic r52 at the pinned revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Upstream theorems are stipulated; the estimates above are new author deductions and still require independent scrutiny before any use in a candidate. No literature novelty claim or finite numerical certification is made.
