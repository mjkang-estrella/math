# Sustained personal ordinary investigation — no full survivor

No mathematical program, enumeration, numerical test, CAS, solver or Lean was used. Hand derivations below are author work, not independent review.

## 359050: exact Conjecture 4.3
Asgarli–Ghioca author PDF pp.6–8 asks: for each r>=2 find m(r), uniformly over q>m(r) with characteristic not dividing r, and some k in Fq giving GEOMETRIC smoothness. Theorem1.8 tests rational smoothness only; Examples4.1–4.2 prohibit replacing the target by that criterion.

Route A, rational counting then extension control. The bad rational parameters are images of x -> (1-x^(r*r+r+1))/x^(r+1) on Fq*. Thus at least one parameter avoids rational singularities. This is the source Proposition1.3 mechanism applied to Theorem1.8, zero novelty. It supplies only one parameter, with no control over nonrational singularities. The source q+3 Bezout proof does not extend to general r. Even a uniform extension-degree bound (source Conjecture4.4) does not alone find one parameter avoiding singularities in that extension.

Route B, base-locus obstruction removed, with full hand algebra. Coordinate-zero projective points cannot be singular: x=0 forces z=0 from F_x=z^(q+r), then y=0 from F_z; y=0 forces x=0 from F_y; z=0 forces x=0 from F_y and then y=0 from F_z. Work at y=1, xz nonzero, and put a=x^q,b=z^q. The affine polynomial is f=a*A+b*B+C, where
 A=x^r*(1-k*z)-z^(r+1),
 B=-1+x*z^r+k*x^(r+1),
 C=z-x^(r+1).
Because a,b have zero derivatives,
 f_x=a*r*x^(r-1)*(1-k*z)+b*(z^r+k*(r+1)*x^r)-(r+1)*x^r,
 f_z=a*(-k*x^r-(r+1)*z^r)+b*r*x*z^(r-1)+1.
The exact singularity test is f=f_x=f_z=0; Euler at y=1 recovers the missing homogeneous derivative, even when p divides r+1.

The pencil coefficient g=x^(r+1)*z^q-x^(q+r)*z vanishes exactly when z=lambda*x with lambda in Fq*. On this line f0=(x^q-x)*(x^r-lambda). A nonrational base point therefore has x^r=lambda. Set mu=x^(q-1); then mu^r=1, mu!=1. Direct substitution gives
 f_z=1-mu*x*(k*lambda+lambda^(r+1)),
 f_x=lambda*(mu*r-(r+1)+mu*x*(k*lambda+lambda^(r+1))).
If f_z=0 then f_x=lambda*r*(mu-1), nonzero under the EXACT target characteristic assumption. Hence every nonrational base point is smooth for EVERY k. Rational base points and nonbase singularities remain. This is a partial lemma, not a candidate.

Route C, nonbase critical values. On g!=0 use h=-f0/g. Nonbase singularities are critical points with value k. Generic smoothness or a discriminant of degree depending on q does not bound bad Fq parameters below q. The three displayed equations are linear in (a,b,1), yielding a determinant of degree bounded in r, but a=x^q,b=z^q retain q-dependent equations. A determinant hypersurface is not a uniform parameter bound. One would need a bounded exceptional nonbase locus after Frobenius compatibility, or a positive-density count of good parameters. Neither is proved. No complete generic Bertini-to-this-pencil bridge was authenticated.

Lean endpoint: for arbitrary finite fields F with cardinal q and q>m(r), characteristic not dividing r, exhibit k for which the homogeneous polynomial and all three derivatives have no common nonzero zero in AlgebraicClosure F. Finite fields, algebraic closures, MvPolynomial and partial derivatives have standard mathlib objects; the source smooth-projective-curve bridge and all quantifiers need authored infrastructure. This is a feasibility assessment, not an import/typecheck result. No endpoint exists.

## 363818: full digit-sum Conjecture5.1
Beierle–Beyne 2407.04570v2, 29Apr2025, pp.4,21–22. Prime p, n>0, M=p^n-1. Positive zero residue is M, not zero. Excluded residue classes make p=2,3 vacuous. The target includes ALL eligible d, not just actual planar exponents.

Route A, generic multiplier. If h>=3 divides d and p-1, choose E=M/h. Its n digits are all (p-1)/h. Since dE is a positive multiple of M, E star d=M. The gain is n*(p-1)*(1-1/h)>n*(p-1)/2. Thus gcd(d,p-1)>=3 is paid by a routine repunit argument, uncredited. For h=2 it gives equality, not strictness; for gcd1 it gives no multiplier. Source Lemma5.3 and its high-weight e=1 branch cover other proper cases, zero novelty. Low-weight gcd1/2 cases remain.

Route B, complement symmetry and averaging. Put N=n*(p-1). For 1<=e<M, s(M-e)=N-s(e). If de is nonzero mod M, d star(M-e)=M-(d star e), so the two gains are opposites. If gcd(d,M)=1, multiplication permutes 1,...,M-1 and the total gain is zero. These identities permit a gain distribution entirely inside [-N/2,N/2]; they do not force the needed witness. Nonunit zero products must return M. Nonplanarity is NOT the converse of source Corollary1.3; its planar classification cannot simply be contraposed to settle digit sums.

Route C, carries and dimension lifting. With cyclically folded convolution of n-digit vectors, carry equations have the form
 b_i=sum_j a_j*d_(i-j mod n)+c_(i-1)-p*c_i.
Summing yields gain=(s(d)-1)*s(e)-(p-1)*sum_i c_i. Independent digit choices fail because carries must close around the n-cycle, with correct all-(p-1) zero normalization. No uniform extremal carry classification is proved.
If m divides n, choose e=E*(p^n-1)/(p^m-1). Repeated m-digit blocks show that multiplication gives repetitions of E star D, where D is the positive representative of d mod p^m-1. Both weights scale by n/m, so strict witnesses lift. Absence of a smaller witness does not imply absence in larger dimension. Primitive dimensions and exceptional smaller reductions remain unpaid.

Exact unpaid lemma: classify every d with max_e(s(e star d)-s(e))<=N/2, placing it in an excluded residue class or one of the printed exceptions. No full witness construction or counterexample is supplied. Bounded search nonmatches are not novelty clearance.

Lean endpoint: forall prime p, n>0, eligible d outside exceptions, exists positive e<=p^n-1 with 2*s(e star d)>n*(p-1)+2*s(e). Natural powers, remainders, digit lists and finite sums have mathlib support; star, the digit-sum wrapper and exception binding must be authored. Comparatively cheap if a proof/witness is found. No formal execution.

## 375405: exact public refutation, zero novelty
Sun 2606.18234v5 Definition1.3 requires vectors nonzero modulo n and exactly n selected indices; Conjecture1.2 is the conjunction of both equalities for every n>2. Li–Ling–Sun–Zhu 2610.19965v1 (arXiv header14Oct2026, internal15Oct2026), Theorem1.1 and full Section2 pp.4–6 give s2(n)>=6n-5>4n+1 for n>=4. This already negates the conjunction irrespective of the unresolved rank-one half.

Actual proof read: repeat each of six vectors +/-(1,0), +/-(0,1), +/-(1,1) n-1 times. P=conv([0,1]^2 union [-1,0]^2) has only zero and its six vertices as lattice points. If n chosen terms sum to a vector divisible by n, their average is integral in P. A vertex average forces all n terms equal, impossible with n-1 copies. Hence the average is zero and the sum also vanishes modulo n^2. Length6(n-1) gives the stated bound. This is attributed public mathematics, not a new witness. Other later Sections3–4 were not deeply audited.
