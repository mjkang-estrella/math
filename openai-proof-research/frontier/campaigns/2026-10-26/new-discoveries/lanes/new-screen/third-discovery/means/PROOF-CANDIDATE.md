# Proposed exact exponent classification (not yet accepted)

MathDB338823, Meštrović–Andjić, arXiv1804.00542v1 Conjecture1.6; latest published Resonance28(12)(2023),1891–1897, online31January2024, DOI10.1007/s12045-023-1726-x, Conjecture1.5. The actual publisher PDF was downloaded and relevant pages visually checked: `../sources/means-resonance-2023-alt.pdf`, SHA256e80be06161e9dc04d3c8f02a967c083086dd3220aa8e03dcd50048fce9d7c232. It retains the same claim, n<0 or n≥1/2 universally valid. Page1893 also retains a separate Seiffert conjecture1.2, not counted here.

Proposed exact universal range: **n≤0 or n≥1**. This is one classification outcome; the explicit witness and component lemmas are not separate discoveries. Latest MathDB full record has zero posted solutions, human solves and progress; all body arrays were inspected. Prior-art review remains required, including any older exact classification beyond this paper's false conjecture.

## Sufficiency

For positive inputs the four source means satisfy H≤G≤A≤Q, A+G≤Q+H and AG≥QH. The latter two inequalities are already source theorems and receive prior credit; they will be proved directly in Lean from the literal definitions.

For n≥1, the pair(A,G) is weakly majorized by(Q,H). Applying the increasing convex function t↦t^n gives A^n+G^n≤Q^n+H^n. For n<0, the logarithmic pair(n log G,n log A) is weakly majorized by(n log H,n log Q): the largest-coordinate comparison uses H≤G, and the sum comparison uses AG≥QH together with n<0. Applying increasing convex exp gives the desired inequality. At n0 both sides equal2. This use of two-point convexity/majorization is classical, not claimed as new.

An independent direct derivative check also confirms sufficiency. Normalize G1,A=c≥1,H1/c,Q=sqrt(2c²−1), and define

D_n(c)=(2c²−1)^(n/2)+c^(−n)−c^n−1.

With t=c^(−2)∈(0,1] its derivative is

D_n′(c)=n c^(n−1)[2(2−t)^(n/2−1)−1−t^n].

For n<0 the bracket is nonpositive. It is increasing in n. At n1 it is nonnegative because 2/sqrt(2−t)≥1+t, equivalent to(t−1)²(t+2)≥0. Thus D_n is nondecreasing fromD_n(1)=0 in both valid ranges.

## Necessity throughout the missing interval

At c1, D_n(1)=D_n′(1)=0 and **D_n″(1)=4n(n−1)**. Thus for every0<n<1, D_n(c)<0 for allc>1 sufficiently close to1. Such c represents actual positive source inputs x=c+sqrt(c²−1), y=c−sqrt(c²−1), whose G1,A=c. This refutes the whole previously asserted range1/2≤n<1, not merely the endpoint wording.

At n1/2 an explicit exact witness is x4+sqrt15,y4−sqrt15. Then A4,G1,H1/4,Qsqrt31. The claimed comparison becomes3≤31^(1/4)+1/2, which is false since31<(5/2)^4. This is an algebraic source counterexample with no numerical certificate dependence.

For completeness, every n>0 also admits pairs satisfying the inequality strictly: as c→∞, D_n(c)/c^n→2^(n/2)−1>0. Hence for every0<n<1 neither direction is universal. This asymptotic observation is not yet a Lean endpoint.

## Current status

Mathematical proof route only. Full Lean and independent source/prior review pending. No discovery count assigned. The original paper's proven integer inequalities are not counted as new.
