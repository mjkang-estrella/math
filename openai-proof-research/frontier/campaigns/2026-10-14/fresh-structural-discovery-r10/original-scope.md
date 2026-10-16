# Frozen original scope: relative complete-intersection Betti extremality C

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0.

Frozen before sustained proof/computation. This is one candidate target,
not a promised theorem.

For every field k of characteristic zero, every n>=1, every integer sequence
2<=a_1<=...<=a_n, every homogeneous regular sequence f_1,...,f_n in
S=k[x_1,...,x_n] with deg f_i=a_i, and every homogeneous proper ideal
I containing (f_1,...,f_n), set R=S/(f_1,...,f_n), M=S/I,
P=(x_1^{a_1},...,x_n^{a_n}), and A=S/P. Let J be the unique
lex-plus-P ideal whose quotient has the Hilbert function of S/I:
in degree d it contains P_d and the lexicographically greatest
dim I_d-dim P_d monomials outside P_d, with x_1>...>x_n.
Existence and ideal closure are stipulated pinned source conclusions.
Put N=S/J, considered as an A-module.

C: for every homological degree p>=0 and internal degree j in Z,

    dim_k Tor_p^R(M,k)_j <= dim_k Tor_p^A(N,k)_j.

There is no bound on n, degrees, homological degree, or additional
generators. All full-length homogeneous complete intersections, all
proper homogeneous quotients, and all characteristic-zero fields are
retained. Infinite relative resolutions, not ambient S-resolutions,
are the subject. No restriction to quadrics, split forms, generic
sequences, finite p, or a subclass will be substituted for success.

Dependencies: openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
The Artinian Lex-Plus-Powers Betti Theorem, thm:main,
cor:characteristic-zero, thm:forms, mono:transfer, mono:bound;
companion Commuting Division-Coefficient Forms, Theorem 1.1 at
its exact construction interface; Murai-Peeva (2012), Theorem 4.6.5
for the pure-power comparison. All new transfer steps must be proved.

Nonroutine operation to attempt: transfer relative Tor from R to a
monomial quotient of A, not just transfer a finite polynomial-ring
resolution. The source's right polynomial-module filtration is not
yet an algebra/module-pair filtration. An alternative via compatible
higher homotopies/Tate differentials would also need proof.

Disposition if unpaid: UNRESOLVED, exact missing transfer retained.
Pure-power cases, ambient Betti bounds and formal change-of-rings upper
bounds are supporting/known material and cannot replace C.
