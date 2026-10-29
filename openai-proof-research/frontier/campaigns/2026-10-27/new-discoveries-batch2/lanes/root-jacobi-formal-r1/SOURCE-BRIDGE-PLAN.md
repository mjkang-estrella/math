# Proposed next bridge: source coefficients to rational midpoint Riccati

This is a proposed algebraic route, not a formal theorem or completed review.
The frozen SourceDefs definitions must remain unchanged. Read the complete
ordinary derivation in sol-jacobi-shifted-denominator-r3/discovery.md and
sol-jacobi-riccati-valuation-r4/PROOF.md first.

One can work in QAlg (w^2=1+x^2) without a separate Laurent embedding:
t=w+x, tInv=w-x, so t*tInv=1. In the Gaussian extension put
xi=(1+i*t)/2, eta=(1-i*tInv)/2. The coefficientwise derivation is
D=2*delta. For the literal factorial polynomials C_s, the ordinary R1 becomes
  delta^2 C_s + i*s*delta C_s + i*delta C_(s+1) - S*C_s = 0,
where S=((u+v)*w^2+(u-v)*w*x)/2. This identity must be PROVED from
P_l and the finite source C_s, not assumed. Exact inverse-factorial conversion
then gives delta^2 F_n+i*delta F_(n+1)-S*F_n=0.

Define scaledH_n by mapping coefficients of the integral h_n through lift,
and substituting a=(u+v)/2, b=(u-v)/2. Its initial term is S and its proved
recurrence is the same delta-Riccati recurrence. Formal logarithmic derivative
comparison should prove delta L_n=i^(-n)*scaledH_n for n>=1. For odd
n=2r-1 this gives delta(Im L_n)=(-1)^r*scaledH_n.

Tau sends xi,eta to their Gaussian conjugates, so tau(Im L_n)=-Im L_n.
Midpoint evaluation sends them to the literal SourceDefs.midpointX/Y, hence
maps generalized L_n to sourceLogCoeff n. These three bridges allow the
closed normalized-primitive uniqueness theorem to identify the source values.
Keep the Gaussian imaginary coordinate distinct from QAlg's w-coordinate.

The substitution with halves is ONLY an identity bridge. Arithmetic must track
the homogeneous degree-d factor 2^(-d) explicitly; do not claim that substitution
preserves integral divisibility. Together with source kappa factor 2^(-n), the
primitive coefficient scaling is 2^(-(n+d)), with the odd-n sign above.
Degree bounds, Catalan leading term, and final valuation assembly can follow.

Mathlib PowerSeries.Log offers logOf f = (log A).subst(f-1), but its usual
derivative is in the spectral series variable. The required derivative acts on
coefficients; a chain/log lemma and identification with the source's explicit
finite powers must be proved, not inferred from that different derivative.
