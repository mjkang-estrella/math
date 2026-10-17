# A technical quadratic approximation-paving deduction

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

This is a prefreeze screen, not a substantial nomination. At pinned revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, family300's approximation companion states quadratic approximation paving for expected masas, while its arbitrary-masa theorem states an epsilon^-6 count. The already proved three-corner operations immediately combine with the expected quadratic statement to yield the following technical variant:

For every epsilon in (0,1), every represented complex von Neumann algebra M, every masa A in M and every self-adjoint x, x is a strong limit of self-adjoint y with ||y||<=5||x||, each admitting an A-paving into at most C epsilon^-2 pieces with diagonal a satisfying ||a||<=||y|| and ||S_P(y)-a||<=epsilon||y||. Constants are universal and the count is chosen before the strong neighborhood. No claim that this quantitative statement is explicitly printed in the source is made.

Here is the complete reduction, to avoid mistaking a missing headline for an unpaid operation. Normalize ||x||=1 and put gamma=epsilon/4. Use exactly the approximation companion's support decomposition e+h=1 and e=f+g, where g annihilates the given test vectors F and an added norming vector xi_0 with ||x xi_0||>3/4. The f-corner masa admits a normal expectation. Apply its quadratic expected-masa approximation corollary there with error gamma/3. It produces y_f arbitrarily close to fxf on fF and fxi_0, with ||y_f||<=3||fxf||<=3, diagonal a_f of norm at most ||y_f||, and

    ||S_(P_f)(y_f)-a_f|| <= (gamma/3)||y_f|| <= gamma.

Its number of colors is at most C gamma^-2. If fxf=0 take y_f=a_f=0. On the h-corner apply the source's no-central-functional corollary with m=ceil(1/gamma), giving y_h close to hxh, ||y_h||<=1 and ||S_(P_h)(y_h)||<=gamma. Put y_g=0 and retain every off-diagonal block of x between f,g,h. This is exactly the source assembly, with a different available f-corner approximant.

The block-diagonal correction y-x has f-block norm <=4, g-block norm <=1, and h-block norm <=2. Thus ||y||<=5. Choose the two approximations so that ||(y-x)xi||<min(delta,1/4) for xi in F union {xi_0}; the g-block contributes zero. Consequently ||y||>1/2. Use disjoint palettes P_f, P_h and {g}, so all retained off-diagonal blocks disappear under pinching and the color counts add. With d=a_f on f and zero on g+h,

    ||S_P(y)-d||<=gamma.

Contractivity gives ||d||<=||y||+gamma. Clip d to [-||y||,||y||], obtaining a with ||a||<=||y|| and ||a-d||<=gamma. Then

    ||S_P(y)-a||<=2gamma=epsilon/2<epsilon||y||.

The total count is C gamma^-2+ceil(1/gamma)+1=O(epsilon^-2). Scale back to arbitrary x, and handle x=0 directly. This proves all displayed quantifiers. It is the existing expected-masa corollary plus the existing no-central-functional and three-corner construction. No substantive new operation is claimed.

Actual source locations: approximation introduction cor:quadratic-expected-approximation; approximation general.tex Lemma gen:support-decomposition, Corollary gen:no-central-approximation, full proof of thm:main and final expected-masa corollary proof. Quadratic introduction and reductions also read in full. Authenticated bytes and Git blobs are in source-receipt.json. Private source files retain third-party rights.
