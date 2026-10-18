# 300: multipaving and quadratic approximation screens

Prefreeze only. No full new target frozen. Two operations were examined.

## Simultaneous paving

The scalar quadratic source does not by itself give one partition for an arbitrary prescribed k-tuple. Independent scalar partitions yield a product count. Paving the diagonal tuple in M tensor M_k over A tensor D_k gives k independently chosen partitions; it does not identify them in A. These are exact interface distinctions, not impossibility claims.

The finite matrix interface is already paid by Ravichandran–Srivastava, Asymptotically Optimal Multi-Paving, arXiv1706.03737v2: Theorem1 has one-sided bound18 k epsilon^-2; applying it to both signs gives a two-sided bound36 k epsilon^-2. Actual extracted introduction lines1–130 and Theorem25/full proof plus proof of Theorem1 lines980–1064 were read. Theorem25 is precisely the finite input imported by source300 polynomials.tex. Its partial-color process uses random (color,sign) at each site and one common matrix T. Extending it to a common finite-family process requires compatible assignment costs, transfer, and final simultaneous compression, not merely inserting k into the final theorem.

No such complete extension was established here. The existing finite theorem and source machinery make a straightforward extension a substantiality risk even if completed; no favorable verdict is presumed. Popa–Vaes1412.0631 Remark5.2(1), actually read, proves the obstruction to a bound independent of family size using powers of a cyclic normalizing unitary (or self-adjoint generators from an elementary2-group). A diagonal subtraction cannot conceal the off-diagonal entries in the finite atomic model. This is not a refutation of linear dependence on k.

## Quadratic approximation without an expectation: source assembly

The approximation companion asserts an epsilon^-6 bound in full generality, and a quadratic bound when a normal expectation exists. Its own general.tex support decomposition and pure-corner lemma already assemble these into a quadratic arbitrary-masa approximation result with norm constant5. This complete technical deduction is recorded, not nominated.

Precisely, there is universal C so that for every represented von Neumann algebra M, every masa A, every self-adjoint x, every0<epsilon<1, every finite vector set F and delta>0, there are a self-adjoint y with norm(y)<=5 norm(x), an A-partition P with at most C epsilon^-2 projections, and self-adjoint a in A with norm(a)<=norm(y), such that y approximates x on F within delta and norm(S_P(y)-a)<=epsilon norm(y).

Proof. Scale norm(x)=1; the zero case is immediate. The source support-decomposition lemma gives e,h=1-e in A, a normal expectation on eMe, and no centralizing normal positive functional on hMh. Fix eta=epsilon/12. The source quadratic-expected-approximation corollary gives y_e on eMe, norm(y_e)<=3, arbitrarily close to exe strongly, with a partition of at most C0 eta^-2 pieces and diagonal d_e, norm(S(y_e)-d_e)<=eta norm(y_e)<=epsilon/4. Its norm bound is relative to norm(exe), hence still <=3. On hMh the source no-central-approximation corollary gives y_h=s(hxh)s, norm(y_h)<=1, arbitrarily close strongly, with m=ceil(4/epsilon) pieces and norm(S(y_h))<=epsilon/4. Retain the original cross corners:

    y=y_e+y_h+exh+hxe.

The difference from x is block diagonal, with norm at most max(4,2)=4, so norm(y)<=5. Apply both strong approximations also to a unit norming test vector xi0 satisfying norm(x xi0)>3/4, with error<1/4. This ensures norm(y)>1/2. Use disjoint palettes on e,h so all cross terms vanish under pinching. With d=d_e+0_h, norm(S_P(y)-d)<=epsilon/4. Clip d in the abelian algebra to [-norm(y),norm(y)], obtaining a with norm(a-d)<=epsilon/4, because S_P is contractive. Consequently norm(S_P(y)-a)<=epsilon/2<epsilon norm(y). Counts add to C0(12/epsilon)^2+ceil(4/epsilon), uniformly before F,delta; absent corners are padded with zero projections. Scale back. Every quantifier claimed here is retained.

All operations are supplied by the companion, including the support decomposition, pure-corner estimate, retaining cross entries until pinching, norming vector, clipping, and quadratic expected result. Its published assembly uses a more precise correction to retain norm constant3; this argument asserts only5. This is an unfrozen technical deduction, not a narrowed substitute for any frozen theorem.

Actual primary comparison: Popa–Vaes arXiv1412.0631, Proposition2.4 statement and selected proof passages for its so-to-approximation direction were read. The expectation assumption is explicit, and its proof builds y=q'(x-a)q'+a with norm<=3norm(x); no unrestricted transfer is inferred from it. The new assembly only applies that source-paid corollary on the expected corner. The remaining expectationless operation is source-paid. No complete full-primary-paper read or literature-priority assertion.
