# Hostile checks and reductions

These checks are part of the author's deduction, not independent review. No
finite computation substitutes for the general proof.

## 1. Why ordinary normal projection is insufficient

At one point consider the realizable two-jet

    F_x=e1, F_y=e2, F_yy=-e1+2e3,

given, for example, by the local embedding
F(x,y)=(x-y^2/2,y,y^2,0) at (0,0). Its metric at that point is the identity,
Gamma^x_yy=-1, and Hess x(partial_y,partial_y)=1. Its velocity plane and projected
x derivative are

    P=span(2e1+e3,e4), v=(4/5)e1+(2/5)e3.

For added primitive amplitude a=1 the prescribed circle radius is 3/sqrt(5).
The point V=-(3/5)(2e1+e3) lies on that circle. At this phase

    w=V-v=-2e1-e3,  X=F_x+w=-e1-e3.

Ordinary orthogonal projection to the old tangent plane sends X to -e1, so
its tangential derivative is not close to the identity. The proof therefore
cannot assert that the Euclidean nearest-point projection has C1-small error.
This checks an allowed phase geometry, not a global counterexample to either
the source or our theorem. Large arcs are allowed in the actual source loop.

The oblique linear base projection is L(q)=(q1-2q3,q2), which kills P. Directly,
L(X)=(1,0) and L(F_y)=(0,1). Section 5 of `proof.md` proves the corresponding
nonlinear estimate uniformly over the whole disk and every source phase.

## 2. All-size oscillations and degeneracies

No assumption |w|<<1 is made. For fixed data w and df_z are bounded, while the
tube displacement tends to zero; this is exactly what (5.2) needs. If v vanishes
in the interior, the complement proof still applies: it uses Gamma^x_yy!=0,
not a normalized v or a division by its norm. The source handles the velocity
loop there. Positivity of the phase Hessian on the compact closed disk provides
the nonzero connection coefficient and an open collar. There is no claim of a
uniform margin over all input metrics.

## 3. Why C0 proximity alone does not solve the problem

An embedded arc or surface can be changed in an arbitrarily small neighborhood
by a tiny self-crossing immersion. Thus a proof using only the exact induced
metric and C0 closeness would omit a genuine injectivity issue. Here the
projected map, rather than the new map itself, is C1-close to F. Its injectivity
forces that of f_z. Positive definiteness of the prescribed metric supplies
immersion, but is not used to assert global injectivity.

## 4. Exterior support, boundary and topology

The source exact correction need not be supported in D. The proof keeps its
exterior C2 error, includes that error in the global r_z, and uses one exterior
anchor to derive C0 convergence. Only the periodic vector w and its primitive W
are extended by zero. No false collar-fixing property is assumed.

The global complement is obtained as a cutoff graph over the normal bundle;
it requires neither a global normal frame nor a trivial rank-two bundle.
The frozen target is orientable because the starting map must embed in S3.
Whitney immersion in R3 would not suffice for this starting step. Extending the
claim to all nonorientable surfaces from this argument is not justified.

## 5. Finite versus infinite assembly

Reach and derivative bounds may deteriorate after each step. At the next step
the old embedding is fixed and compact, hence has its own positive tubular
radius and C1 stability neighborhood. The number of source steps is finite;
choose each z after the old map is fixed. No infinite limiting embedding theorem,
uniform reach, continuous selection in z, or diagonal subsequence is used.
Disconnected surfaces have finitely many components, whose final compact images
can be separated by translations without changing their metrics.

## 6. Known reductions and remaining review questions

General position of a surface in R4 alone leaves possible double points and
does not prove injectivity here. Nash C1 or C^(1,alpha) embedding theorems do not
give smoothness. Moving to R5 would not solve the frozen target. The proof uses
none of these replacements.

Conversely, a standard embedding-preservation argument plus the source's exact
smooth operations may make this result technical. The question for a contribution
reviewer is not whether the global conclusion sounds stronger, but whether
Sections 3–5 represent enough additional mathematics beyond the paid source
geometry and classical corrugation methodology. That judgment is unresolved.
