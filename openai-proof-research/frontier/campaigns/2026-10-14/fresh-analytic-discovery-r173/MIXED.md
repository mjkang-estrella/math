# r173 — one support choice for all mixed terms

These are prefreeze deductions after the recorded source/primary reading. They extend the finite-column calculation far enough to test actual compatibility, without claiming novelty for finite-tuple diagonalization.

## 1. Nested supports preserve all earlier estimates

Let B satisfy P, let a,b be positive contractions, let c_1,...,c_q be a finite list in B, and fix 0<delta<1/2. Let a_*,b_* be ramps zero on [0,delta] and one on [2delta,1]. For kappa>0 we construct positive contractions p in Her(a_*) and q_0 in Her(b_*) such that

    ||e_p c_l e_(q_0)||<kappa for every l,                     (1.1)

and every representation detecting (a-2delta)+ has norm one on p, with the analogous assertion for b and q_0.

For the first entry apply source prop:iterated-separation to a_*,b_*, c_1/max(1,||c_1||) with tolerance kappa/max(1,||c_1||). Given p_j,q_j, apply that proposition to p_j,q_j and the next normalized entry, with the corresponding tolerance. Its output lies in Her(p_j),Her(q_j), so e_(p_(j+1))<=e_(p_j) and likewise on the right. Sandwiching an earlier mixed term by these two smaller projections cannot increase its norm. Norm-one signals persist since they are above the proposition's 1/2 threshold. The hereditary inclusions also preserve the original high spectral support. This proves (1.1) for the final pair. For an empty list use a_*,b_* themselves.

This is a finite construction. At each use the source's internal iteration chooses k with max(1,||c_l||)theta^k below the requested tolerance, and implements the rescaled element inside B by cutoff functions of the current supports. It never treats e_p c e_q, which need not be an algebra element, as the next algebra input. The number k is finite but not numerically evaluated because theta is not evaluated in the source.

## 2. Rectangular implementation, with the whole matrix norm controlled

Write d_a=(a-2delta)+ and d_b=(b-2delta)+. The signals and primitive-ideal criterion give d_a in Id(p). Since pap>=delta p², Id(pap)=Id(p). P makes pap properly infinite. For every finite m the source proper-target comparison therefore gives

    diag_m(d_a) subequivalent to pap.

Fix 0<rho<=2delta. Rectangular corner compression of a comparison sequence gives W in M_(1,m)(B) with

    ||W*papW-diag_m(d_a)||<rho.

Put R=pW. This is an algebra row supported by e_p on the left, and

    delta R*R<=R*aR,
    ||R||²<=(1-2delta+rho)/delta<=1/delta,
    ||R*aR-diag_m(a)||<2delta+rho.                            (2.1)

The norm of diag_m(d_a) is ||d_a||, not m||d_a||. The same construction with q_0,b and any finite n gives Q in M_(1,n)(B), supported by e_(q_0), with identical bounds. Consequently

    ||R*c_l Q|| <= ||R||||Q||||e_p c_l e_(q_0)||
                 <kappa/delta                               (2.2)

as a norm estimate in M_(m,n)(B). It has no m*n factor. This is the missing compatibility step in the naive plan of compressing both columns independently: independent rows have no mixed support estimate at all. Here the support separation precedes the comparison coefficients, and their final uniform bounds validate that order of choices.

If a cutoff is zero, its ideal comparison allows a zero row; the same conclusions hold. Scaling handles noncontractive a,b, with the scaling explicitly affecting diagonal error. The argument itself uses neither unitality nor separability nor nuclearity nor exactness.

## 3. Insert the actual patched columns

Let S in M_(m,1)(B) and T in M_(n,1)(B) have norms at most L, where L>=1. Suppose their diagonal patching errors relative to prescribed positive targets a_0,b_0 are less than e_0:

    ||S*diag_m(a)S-a_0||<e_0,
    ||T*diag_n(b)T-b_0||<e_0.

Set u=RS and v=QT. Equations (2.1)–(2.2) give

    ||u*a u-a_0||, ||v*b v-b_0|| <e_0+L²(2delta+rho),
    ||u*c_l v||<L² kappa/delta,
    ||u||,||v||<=L/sqrt(delta).                              (3.1)

For any e>0, take e_0<e/4, 0<delta<min(1/4,e/(12L²)), rho=delta, and kappa=delta e/(4L²). Then diagonal errors are <e/2 and each mixed error <e/4. The local columns are chosen first, so L is known before the support precision is selected. All constants refer to actual norm comparisons; no tracial or rank approximation appears.

For compact parameter data B=C(K,A), the finite-cover columns from CALCULATIONS.md supply S,T. Each c_l is itself a continuous algebra element. The rows are constructed in this SAME B, so their output coefficients are continuous in K automatically. No selection theorem for independently chosen pointwise rows is being assumed. The tensor-permanence premise for B was checked in CALCULATIONS.md.

## 4. Stronger primary payment and the remaining interface

Kirchberg–Sierakowski v2 Remark3.2(i) records the stronger contractive arbitrary-entry diagonalization; its Lemmas5.2–5.6 carry finite tuples, repeated multiplication, and finite mixed lists with cutoff/norm control. The complete proofs in physical pages14–25 were read. Kirchberg–Rordam 2002 Sections7–8, read visually where text recovery failed, already include commuting-copy construction, abelianization, collapse of approximately inner maps to one step under nuclear control, and the absorption intertwining. Thus (3.1) is not nominated on the ground that m,n,q are large or that the coefficients are bounded. Those features have actual prior mechanisms.

What (3.1) preserves is one positive diagonal on each side and the vanishing of finitely many cross expressions. It does not preserve an arbitrary noncommuting family of diagonal observables with the SAME implementing row. Nor does it fix a preassigned row at a closed parameter subset. The rows R,Q are free to change defect projections and phases, subject only to the displayed comparison and support conditions.

The distinction can be quantified. For an isometry V and selfadjoint d in a unital algebra, suppose

    ||V*dV-d||<=eta,  ||V*d²V-d²||<=eta.

Then the exact expansion

    (dV-Vd)*(dV-Vd)=V*d²V-V*dV d-dV*dV+d²

gives ||dV-Vd||²<=eta(1+2||d||). A simultaneous moment construction for d and d² would therefore provide approximate commutation. Our support-separated comparison does not supply those two moment estimates: its one diagonal is a or b. Applying it to d and then d² chooses new coefficients and loses the first moment. Merely listing more cross terms does not repair this.

The actual KR2002 proof shows where stronger data enters. Proposition7.13 abelianizes while fixing commuting controls, Proposition7.14 collapses an abelian-range approximately inner map, and Lemma7.18 uses nuclearity of its domain in the maximal/minimal tensor and tensor-ideal argument before Theorem7.21 supplies the general nuclear-domain collapse. Exactness alone is not the nuclearity step in that proof. No hypothesis-removal theorem, nonnuclear relative-commutant theorem, or uniform central witness is inferred here. These observations describe an unpaid interface of this construction, not a claim that every other construction must fail.
