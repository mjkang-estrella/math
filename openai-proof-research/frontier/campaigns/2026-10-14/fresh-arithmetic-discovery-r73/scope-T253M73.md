# Frozen full target T253M73

Status at freeze: UNPROVED. No nomination or count credit.

Fix tau=(1+sqrt(5))/2 and O=Z[tau]. For EVERY positive integer a satisfying the pinned source253 condition (lambda-choice), set lambda=tau^a. Let X_a, F_(a,m), A_(a,m) be exactly its Boolean polygon Stone space, full piecewise translation group on m tracks, and alternating subgroup, using the four forms x,y,y-lambda*x,x-lambda*y and levels in O. For EVERY finite integer m>=1, the proposed integral Schur multiplier formula is

    H_2(A_(a,m); Z) = Z direct-sum (Z/2)^(M_a+9+2 epsilon_a),

up to abstract abelian-group isomorphism, where

    M_a = abs(Norm_(Q(sqrt(5))/Q)(1-tau^(2a))),
    epsilon_a = 1 if 3 divides a, and 0 otherwise.

Equivalently M_a=L_a^2-2(-1)^a-2, where L_a is the Lucas number. No rationalization, unspecified finite torsion, order-four ambiguity, sufficiently-large-m restriction, subsequence of a, or conditional stable splitting replaces this conclusion. The group is not changed. There are no new estimates or hidden constant dependencies.

This is an algebraic group-homology target, distinct from r34's unresolved type-F_infinity target. Its proof would not establish r34.

## Feasibility and chronology

Before this freeze, actual proof bodies in families009,198,008 and253 were screened. The source253 geometry, simplicity, and complete homology proof were read, along with Li's Theorem5.18, Theorem5.19, Corollary5.20, Corollary6.5 and the low-degree setup of Theorem6.12; Gahler-Hunton-Kellendonk Theorem5.3 and proof were read. Preliminary scratch calculations predicted a corner exact sequence and its exterior-square Smith factor F_(2a). These exploratory calculations PRECEDE this freeze. They are not retrospectively presented as a frozen theorem.

The method to test is concrete: complete the source's injective corner map to a finite-orbit exact sequence, compute its integral translation homology, then retain the stable sphere-spectrum information in the actual string/bar model rather than only its integral homology. Li supplies the transfer from that spectrum's pi_2 to the Schur multiplier on every fixed track space. The finite stable attaching maps and two-primary extensions are the unpaid operation; they are not assumed zero. The prediction above is the value suggested by a split model, not a deduction from the paid homology theorem. This method has a finite explicit module/arithmetic part; its stable refinement may fail. If it does, the full formula remains unresolved or is refuted, without shrinking the target.

Primary comparison is bounded; no novelty or substantiality verdict is claimed. The source and all pinned operations are stipulated true and are not audited. Public original notes and private third-party bytes remain separate.
