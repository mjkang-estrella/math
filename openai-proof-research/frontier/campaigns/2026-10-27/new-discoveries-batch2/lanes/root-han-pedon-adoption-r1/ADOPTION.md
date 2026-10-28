# Han–Pedon higher-shift handback — root assessment, 28 October 2026

Root read the completed pi-han-pedon-higher-shifts-r1 report and completed
thread. Preserve it as UNCREDITED research material. There is no full proof
or refutation of Conjecture C, no general unboundedness theorem E(2), and no
literal Lean endpoint. Accepted count stays2/30 additional,32/60 total.

The universal Desnanot–Jacobi T-system is correct and classical. With
A_k=Delta_k^(s), B_k=Delta_k^(s+1), X_k=Delta_k^(s+2), it reads
A_(k+2) X_k = A_(k+1) X_(k+1) - B_(k+1)^2.
Hence when A_(k+1)!=0,
X_(k+1)=(A_(k+2) X_k+B_(k+1)^2)/A_(k+1).
But when A_(k+1)=0 and A_(k+2)!=0, the correct singular determination is
X_k=MINUS B_(k+1)^2/A_(k+2). Proposition2(b) in the report omits this minus.
Root's own coefficient-recursion / integer-Bareiss implementation verifies
192 T-system identities and exhibits failures of the report's positive-sign
formula, e.g. n=2,s=3,k=0: A_1=0,A_2=-1,B_1=1,X_0=1.
See independent_check.py and independent-checks.json. Do not adopt the
report's entire Proposition2 as a proved result without this repair and a
complete treatment of its singular and periodic-monodromy conditions.

Finite residue fits do not prove any all-index polynomial formula, eventual
nonperiodicity or unboundedness. Claims that the orbits drift FOREVER or
that unboundedness is CONFIRMED are computational conjectures only, unless
an all-index invariant/closed orbit parametrization is actually established.
Root independently checked only the m=0,1,2 instances of the ell5,r0 fit;
these agree as1,15,45. No general quasi-polynomial conclusion follows.

The report's cross-validation scope must also be kept precise: direct Bareiss
comparisons run only to j15–40 in the listed examples, while larger data up
to about440 use the NextABC extraction. Thus every larger value was not
independently checked by a separate direct determinant calculation. The
finite difference fits and reported minimum/Fibonacci degree pattern remain
diagnostics, not theorems or a proof of the proposed degree law.

The original already-proved ell=n+2 periodic case remains excluded. The
unresolved double-zero classes and higher-shift orbit parametrization are
useful next mathematical obstacles, but no parameter-instance/helper credit,
formal investment or literature-priority claim is warranted by this handback.
No external posting or problem-status mutation is made.
