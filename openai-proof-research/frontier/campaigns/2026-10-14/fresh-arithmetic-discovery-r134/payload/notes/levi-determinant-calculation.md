# Prefreeze: retain the Levi determinant and linear correction

The source proof's parabolic input is D(det RΓ(X,(g|M)_E)^s), not D(det RΓ(X,m_E)^s). This distinction survives even for a torus, whose adjoint representation alone has zero trace form. Source §§2–3 were read in full. GLC III v1 §§11.1–11.4, including its line-bundle proof and natural map proving the arbitrary-level unipotent/localization comparison, were read before this derivation.

## Determinants and inertia

For a parabolic P with Levi M, the M-module decomposition is

    g|M = m direct-sum n_P direct-sum n_P^*.

For d(E)=det RΓ(X,E), the restricted line is exactly

    L_(G|M)=L_M tensor d(n_P,E) tensor d(n_P,E^*).

By Serre duality with this determinant convention,

    d(E^*) = d(E tensor omega_X),

so the two nilradical contributions cannot be discarded. Let Q_G be the trace form of the ambient adjoint representation. For any central cocharacter z of M, its weight on L_(G|M) at degree u is Q_G(z,u); the genus term cancels by self-duality. Positivity gives a nonzero integral weight for a degree with nonzero rational central part. The source Kummer test at irrational s then kills that entire component. This kills nontorsion Levi degrees and nonzero compactification defects by the same mechanism, with spectator coefficients retained.

For G=SL2 and M=G_m, let the torus bundle be a line L of degree d and use z(t)=diag(t,t^(-1)). Then

    g_E = O_X direct-sum L^2 direct-sum L^(-2),
    weight_z L_(G|M)
      = 2 chi(L^2) - 2 chi(L^(-2))
      = 2(2d+1-g)-2(-2d+1-g) = 8d.

In the main theorem convention s=(c-2)/4, the exponent seen by this inertia is 8ds=2d(c-2), nonintegral for every nonzero integer d when c is irrational. In the source assembly convention s=(c+2)/4 it is 2d(c+2); the two differ by 8d and have the same integrality obstruction. Thus all nonzero degree torus components of THIS restricted determinant category vanish. This is not a vanishing result for arbitrary twisted torus categories, and does not mean the surviving degree-zero category is zero.

## The half-canonical and rho correction is also paid

For a vector bundle E of rank r and a line A on X, the determinant-of-cohomology identity used in GLC III (11.5) is

    d(E tensor A) = d(E) tensor d(A)^r tensor d(O)^(-r)
                    tensor Weil(det E,A).

Fix theta^2=omega_X. For E=(n_P^-)_(E_M), det E is the character -2 rho_P of M. Consequently

    d(E tensor theta) tensor d(E)^(-1)
      = d(theta)^r tensor d(O)^(-r)
        tensor Weil((-2 rho_P)(E_M),theta).

This explicitly records the coefficient-dependent linear twist. Its constant factors belong to the normalized l_(N_P^-); the variable factor is the rho-line in GLC III Proposition 11.3.4. Tensoring by det(T^*(Bun_(P^-)/Bun_M)) changes the ambient/Levi critical conventions with the displayed rho correction. The primary then constructs a natural map by dualizing restriction of global sections; its vacuum-insertion extension and the unipotent localization theorem make it an isomorphism (Theorem 11.2.3). Corollary 11.2.5 is an ARBITRARY-LEVEL constant-term/localization compatibility. It is already available at the irrational levels used here.

One must not call this an unavailable quantum BRST/globalization operation. The primary explicitly specializes to the critical level only in §11.5 for the enhanced version. Likewise its main Langlands/Eisenstein compatibility has target IndCoh_Nilp of local systems at the classical level. That assertion is not a theorem about Source069 reciprocal-irrational bundle categories just by substituting c.

## What is obtained after using both inputs

Let L_G be the source normalized localization quotient, and let C_P be a geometrically normalized constant-term functor with the appropriate restricted form, determinant, rho line and shift retained. The actual primary comparison computes C_P L_G by a Levi localization of a BRST/Jacquet functor, including moving-point/vacuum integration. Source §3 additionally supplies continuous first/second adjoints and extraordinary-diagonal functional equations. These pay the global descent and adjunction parts of an attempted parabolic construction once its local enhanced comparison has been given.

The operation not supplied here is an identification, at reciprocal irrational forms, of that BRST/Jacquet kernel and the geometric dual-group enhanced Jacquet kernel compatible with their Levi actions and factorization maps. The rank-one screening calculation carries their underlying W-level comparison to an actual chain isomorphism. It does not supply the enhanced comparison with its correctly retained residual torus/Levi structure; that comparison is not a nonexistent Heisenberg-linear map between differently charged Fock terms. A full-scope parabolic theorem has not been frozen.
