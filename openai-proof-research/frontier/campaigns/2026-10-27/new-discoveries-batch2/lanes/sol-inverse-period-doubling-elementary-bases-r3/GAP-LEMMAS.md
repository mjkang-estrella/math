# Complete gap classification (ordinary proof proposed)

Use the literal Table 1 automaton, with padded initial state S, and the suffix sets A_q(t) and extrema table of r242, reproduced in PROOF.md. Put p=2^t. A suffix set is ordered in increasing numerical order. Let G_q(t) be its set of consecutive distances, and M_q(t)=max(G_q(t) union {0}). For children r,s there is the exact recurrence

    G_q(t+1) = G_r(t) union G_s(t) union B_q(t),
    M_q(t+1) = max(M_r(t), M_s(t), max(B_q(t) union {0})),

where B_q(t) is empty if either child is empty, and otherwise is the singleton

    {2^t + min A_s(t) - max A_r(t)}.

An empty/singleton child has no internal gaps. Translation of the right block preserves its internal gaps. If both blocks are nonempty, precisely one consecutive pair crosses their boundary: the maximum of the left child and minimum of the right. These observations prove the recurrences, including all empty-state cases. They also give maximum internal gap recurrences without assuming any finite-prefix extrapolation.

For t>=3 the extrema table gives the following COMPLETE cross-boundary list. A dash means empty B; columns are child depth t, not parent depth t+1.

| q | even t (t>=4) | odd t (t>=3) |
|---|---|---|
| S | 4 | 6 |
| 2 | p/2+4 | 6 |
| 3 | p+2 | — |
| 4 | p/2+4 | 6 |
| 5 | p/2+4 | 6 |
| 6,7,8 | — | — |

For example row 2 uses children 3,4: in the even case p+1-(p/2-3)=p/2+4; in the odd case p+5-(p-1)=6. Row 4 uses children 3,2 and row 5 children 3,5, giving the same formulas. Row 3 has children 5,6: the even cross gap is p+(p-1)-(p-3)=p+2, while at odd t state 6 is empty. Row S uses S,2, giving p+1-(p-3)=4 or p+5-(p-1)=6. States 6 and 7 have an empty left child 8; 8 has two empty children. Thus every row and boundary is accounted for.

The low levels follow directly from A_q(0)={0} for q in {2,6} and empty otherwise. At child depth 0 no boundary exists. At child depth 1 the only boundary is row 2, distance 2. At child depth 2 the only boundaries are row S, distance 4, and row 3, distance 6. There are no hidden low-level larger distances.

Induction on depth using the G recurrence therefore bounds EVERY suffix-set distance by the alphabet

    {2,4,6} union {2^s+4 : s>=3 odd} union {2^s+2 : s>=4 even}.

For any two consecutive global accepted positions a_j,a_(j+1), take n large enough that both are below 2^n. They form a consecutive pair in A_S(n); hence this induction covers every global gap, regardless of its location or most recent common prefix. In particular it covers gaps crossing any larger blocks, including intervals between successive C_t. This is an all-depth cover, not a check of the initial eight blocks alone.

Since c_j=a_j-j-1, every consecutive c-distance belongs to

    {1,3,5} union {D_t : t>=3},
    D_t=2^t+1 for even t, and 2^t+3 for odd t.

Conversely r242's first-threshold identity realizes every D_t at C_t=5*2^t-2F_(t+2)-2. The first accepted positions 1,5,7,13 give c=0,3,4,9 and realize 3,1,5 respectively. Thus the displayed alphabet is EXACT.

The D_t are strictly increasing, with D_3=11, and D_t<2^(t+1). The reviewed identity says all gaps starting before C_t are <=2^t-1 and the gap starting at C_t is D_t. Therefore it is the first occurrence of D_t and a strict record. If C_t<x<C_(t+1), the first-threshold identity for t+1 bounds the gap starting at x by 2^(t+1)-1. The complete alphabet then bounds it by D_t: there is no alphabet value strictly between D_t and D_(t+1). Thus it cannot be an intermediate strict record. Also C_t<C_(t+1), since the D_t gap is <=2^(t+1) and cannot be the first gap exceeding that next threshold. The C_t tend to infinity, e.g. from F_n=O(phi^n), phi<2. The initial gap alphabet <=5 adds only finitely many records. Hence the strict record values greater than 5 are EXACTLY {D_t:t>=3}, and their locations are exactly C_t. No countermodel to root's proposed classification remains in this argument.
