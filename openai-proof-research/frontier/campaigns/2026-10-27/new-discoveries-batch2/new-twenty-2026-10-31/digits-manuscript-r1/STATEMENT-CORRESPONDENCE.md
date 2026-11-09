# Exact correspondence

All declaration names below have namespace `Digits356756`.

| Declaration | Correspondence |
| --- | --- |
| SourceDigit | Natural representative t <= (p-1)/2 or t = (p+3)/2. |
| SourceSet | Fin n -> ZMod p, support in D, each D-fibre of cardinality n/((p+3)/2). |
| energy | Integer E(t)=4t^2-(12k-2)(-1)^t. |
| gap_nonneg | Nonnegative local gap and zero implies all four digits equal. |
| full_scope | All SourceSet vectors in a four-term progression coincide, for p>=13, p%4=1. |
| mathdb_356756 | Negation of existence of four SourceSet vectors with the two zero second differences and a != b; prime and dimension-divisibility hypotheses retained. |
| no_affine_progression | Actual affine progression x+j*r with j:Fin 4 and r != 0 is impossible. |

Source Definition 2.1 counts h digits exactly n/h times. Under h|n these disjoint fibres exhaust all n coordinates, proving equivalence of the explicit SourceSet membership conjunct. For p=4k+1 and k>=3, h=2k+2 and every digit is <p; ZMod.val representatives match the listed digits. digit_bridge and dvd_bridge prove the representative and modular-to-integer bridges. same_histogram and sum_same prove potential-sum equality.

The second differences imply c=2b-a and d=3b-2a. Taking x=a and r=b-a gives the affine parameterization; a!=b iff r!=0. Conversely ring identities prove both second differences for affine progressions. Nonzero r gives four distinct terms for the eligible prime moduli.

At n=0 there is one empty vector and no nonzero r. full_scope does not use primality or h|n; mathdb_356756 keeps both as intentionally unused assumptions. Ordinary proof additionally establishes equal histograms with arbitrary common digit multiplicities; that strengthened predicate is not a separate frozen Lean endpoint. The size corollary, source theorem restatements and literature comparisons are not formalized here.

Only propext, Classical.choice and Quot.sound are allowed. AuditFull covers all local generated declarations in Digits, not just named endpoints. Cached upstream dependencies remain trusted.
