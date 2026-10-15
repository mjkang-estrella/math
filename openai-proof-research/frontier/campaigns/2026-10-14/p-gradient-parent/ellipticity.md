# Exact supporting ellipticity calculation

For I345 Section 7, let the unit lift direction be xi=(a,b), with
|a|^2+b^2=1 and b>=b0>0, and let e lie in [0,1]. Its zero-jet
quadratic form at a vector (h,s) is

    Q(h,s)=s^2+|h|^2+e s^2-(a.h+b sqrt(e)s)^2.

If a is nonzero, split h=x a/|a|+h_perp, and put A=|a|,
y=|h_perp|^2 and t=sqrt(e). If a=0, any orthogonal coordinate
split works. Then

    Q=y+(b x-t A s)^2+s^2.

The following explicit bounds hold at every parameter endpoint:

    (b0^2/3)(|h|^2+s^2) <= Q(h,s) <= 2(|h|^2+s^2).

For the lower bound, put N=y+x^2+s^2. Direct expansion gives

    3Q-b^2 N
      =(3-b^2)y+(b x-2t A s)^2+(b x-t A s)^2
                         +(3-b^2-2t^2 A^2)s^2.

All terms are nonnegative: A^2+b^2=1 and t^2<=1 imply
3-b^2-2t^2 A^2>=0. Replacing b^2 with b0^2 preserves the bound.
For the upper bound, the two-dimensional Cauchy–Schwarz identity gives

    (b x-t A s)^2 <= (b^2+t^2 A^2)(x^2+s^2) <= x^2+s^2.

The first inequality's difference is (b s+t A x)^2. Adding y+s^2
gives the asserted upper bound.

`../formal/FrontierSupport/LiftedEllipticity.lean` checks these real
polynomial statements, including the lower constant b0^2/3. It does not
formalize the orthogonal coordinate split or any PDE theorem. The calculation
is an explicit version of a claimed supporting estimate, not a new frontier
result. Full proof and novelty acceptance remain pending.
