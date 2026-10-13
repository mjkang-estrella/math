# I233 — parent calculation for the viscous limit

**Partial conditional reduction, not a finding or a proof of I231.** This calculation is independent of the live I230/I231 outputs. No contribution or prior-art claim is attached.

For a smooth function v(x,t), x in R^d, put w=v_t+|D_xv|^2/2 and

    F[v]=D^2v[(D_xv,1),(D_xv,1)].

Direct differentiation gives F[v]=w_t+D_xv.D_xw. Consequently, for fixed tau>0,

    F[v]+tau Delta_x v=0

is exactly the Euler–Lagrange equation of the strictly convex gradient integrand

    L(p,q)=exp((q+|p|^2/2)/tau).

Indeed L_q=L/tau and L_p=Lp/tau, so partial_t L_q+div_x L_p=L(F[v]+tau Delta_xv)/tau^2. Its gradient Hessian has quadratic form

    D^2 L(p,q)[(xi,eta)] = L[(p.xi+eta)^2/tau^2+|xi|^2/tau],

which is positive definite. It is not uniformly elliptic over unbounded gradients; no regularity theorem is inferred from strict convexity alone.

The equation is invariant under adding constants or a multiple of t, under isotropic scaling v_R(x,t)=v(Rx,Rt)/R, and under the Galilean change

    v^a(x,t)=v(x+a t,t)-a.x-|a|^2 t/2.

For the last identity, D_xv^a=D_xv-a and w^a=w(x+a t,t). Hence the material derivative partial_t+D_xv^a.D_x becomes partial_t+D_xv.D_x on w, and Delta_xv^a=Delta_xv. These are classical identities; extension to viscosity solutions requires checking smooth-test transformations, not differentiating a nonsmooth solution.

Suppose v has the exact I231 all-center/all-radius shear-fit property with error C0 R. At the origin choose p_R,q_R with

    |v(h,l)-v(0)-p_R.h-q_R l|<=C0 R
    for |l|<=R, |h-p_R l|<=R.

At l=0, comparison of the R and 2R fits on |h|<=R gives |p_R-p_(2R)|<=3C0. For dyadic R tending to infinity, therefore |p_R|=O(1+log R).

The normalized functions

    u_R(X,T)=[v(RX+R p_R T,RT)-v(0)
                -R p_R.X-R(q_R+|p_R|^2)T]/R

satisfy |u_R|<=C0 on the unit product cylinder and the same viscous equation. If this bounded family admitted a common interior modulus of continuity for D_Xu_R, then v would be affine. For a fixed (h,l), its transformed coordinate is ((h-p_R l)/R,l/R), which tends to zero by the logarithmic bound. Thus the common modulus would imply D_xv(h,l)=D_xv(0,0). It would follow that v(x,t)=p.x+g(t), and the equation would reduce to g''=0.

**Unpaid lemma:** bounded solutions of the fixed-tau viscous equation on a unit cylinder have classical spatial derivatives with an interior modulus depending only on tau, d and their oscillation. This is not supplied by I224's forced infinity theorem, since the transverse Laplacian is not bounded a priori. Nor does mere strict convexity of L supply it. A full-space fit theorem remains unproved here until that lemma or a different rigidity argument is paid.
