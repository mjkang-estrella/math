# Dimension-uniform local algebra calculation

Author supporting lemma only. It does not extract algebraic errors from the nonlinear Gaussian curl or prove the full prospective entropy statement.

Let T be a real fully symmetric cubic tensor on R^m. Put (X_r)_{ij}=T_{rij}, B(T)=sum_r X_r^2, and

    R(T)^2=||B(T)-I||_F^2+sum_{r<s}||[X_r,X_s]||_F^2.

Let O={sum_i u_i^tensor3 : (u_i) an orthonormal basis}; signs are included by changing u_i. Then

    dist_F(T,O)<=1/sqrt(6)  =>  dist_F(T,O)<=sqrt(2) R(T).  (L)

Proof. The compact orbit has a closest point; rotate it to T0=sum e_i^tensor3 and write T=T0+H. First variation makes H perpendicular to the orbit tangent. For i<j write a=H_iij,b=H_ijj; rotation in the ij plane has opposite signs in these two slots, so orthogonality says a=b. Write d_i=H_iii and c_ijk=H_ijk for distinct indices. More generally the squared normal projection is

    sum d_i^2 +(3/2)sum_(i<j)(a+b)^2 +6sum_(i<j<k)c_ijk^2.

The linearization D B has diagonal 2d_i and ij entry a+b. The commutator derivative at pair r<s is [E_rr,H_s]+[H_r,E_ss]. Its rs entry is a+b and its sr entry is its negative. For each third index t it has entries rt=c, tr=-c, st=-c, ts=c. Therefore

    ||D B||_F^2 =4sum d_i^2+2sum(a+b)^2,
    sum_(r<s)||D comm_rs||_F^2=2sum(a+b)^2+12sum c_ijk^2.

Their sum is at least twice the normal squared norm, hence at least 2||H||_F^2 for the closest-point H. The quadratic remainder in B has norm at most sum_r||H_r||_F^2=||H||_F^2. The squared commutator remainder sum is at most

    4sum_(r<s)||H_r||_F^2||H_s||_F^2<=2||H||_F^4.

The combined remainder is at most sqrt(3)||H||_F^2. Thus R(T)>=sqrt(2)d-sqrt(3)d^2>=d/sqrt(2) when d<=1/sqrt(6). All sums/norms are unnormalized; no constant depends on m. This proves (L).

The premises matter: source first-chaos coefficients need not yet form a fully symmetric tensor; small differential curl only gives a negative-order control on q(L), not the exact symmetry or small R(T). Also (L) assumes distance already below an absolute radius. Global approximate-associativity, or a global route into this neighborhood from the analytic defect, remains unpaid. Classical exact odeco characterization is credited to Boralevi–Draisma–Horobet–Robeva (actual Section3.1 read), not claimed here as new.

# Returning from nonlinear normalization

Parent author assistance, independently checked here: if centered X and Z both have covariance I, P is symmetric positive definite, and a coupling satisfies E|PX-Z|^2=epsilon^2, then the SAME coupling satisfies E|X-Z|^2<=4epsilon^2. Diagonalize P by an orthogonal map; each coordinate X_i,Z_i has L2 norm1. Reverse triangle gives |p_i-1|<=||p_i X_i-Z_i||_2. Thus ||X_i-Z_i||_2<=2||p_i X_i-Z_i||_2. Sum squared inequalities. No bound on P inverse or dimension is needed.

Consequently, once a normalized centered transport is close to an isotropic rotated centered exponential map, quantitative return to the original isotropic law costs only4. The earlier first-interfaces note's normalization debt is resolved at this coupling level; approximation and the main nonlinear compatibility debt remain.
