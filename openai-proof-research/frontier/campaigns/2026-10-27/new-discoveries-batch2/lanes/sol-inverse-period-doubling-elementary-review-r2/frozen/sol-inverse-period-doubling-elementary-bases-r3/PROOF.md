# Revised elementary ordinary solution; HOLD pending independent review

Claim. The increasing enumeration b of the zero positions of the compositional inverse of the period-doubling word is not k-regular over Z for any integer k>=2. This answers Rampersad–Stipulanti, JIS21 (2018), Article18.9.1, Problem27 negatively. No literature-priority or campaign acceptance claim is made.

All indices start at zero; F_0=0,F_1=1. Scientific input hashes are in bindings.json and immutable-source-references.json; the latter reuses verified frozen primary bodies without recursive duplication. Source Table1 and Propositions3,10,16 are used as published results. The inherited r242 argument is the first-threshold endpoint calculation and synchronized pumping contradiction. This revision adds the complete gap alphabet and elementary arbitrary-base reduction proposed by root; it does not claim a new discovery or campaign acceptance.

## 1. Exact coding and compression

Let u be the inverse word, a_j its increasing one positions, b_j its increasing zero positions. Table1 accepts canonical MSB-first binary representations of a_j, with states2,6 final. Its transitions on0,1 are 1:82,2:34,3:56,4:32,5:35,6:87,7:86,8:88. Replace initial1 by S with transitions S:S2. Reading leading zeroes in S has no effect. Thus the 2-uniform fixed point w of

    S->S2,2->34,3->56,4->32,5->35,6->87,7->86,8->88

codes u under final-state indicator {2,6}. This also confirms the literal language {11}*1 union 1{1,00}*0{11}*1 following Definition15. In particular all a_j are odd, and even positions of u are zero.

For g_n=b_(n+1)-b_n, g has value2 exactly at

    c_j=a_j-j-1.

Indeed the one at a_j is isolated between zeroes a_j-1,a_j+1; there are a_j-j preceding zeroes, so a_j-1 has rank a_j-j-1. Every gap2 arises this way; every other gap is1. Consequently

    c_(j+1)-c_j=a_(j+1)-a_j-1.

Equivalently each pair (u_(2n),u_(2n+1))=(0,v_n) contributes gaps11 if v_n=0, or2 if v_n=1. The second-child final-state indicator gives exactly

    g=H(w), H(S)=H(3)=H(4)=H(7)=2,
    H(2)=H(5)=H(6)=H(8)=11.

This does not assert closure of automatic words under variable-length morphisms.

## 2. Block extrema and counts: an all-t calculation

For q a state, let A_q(t) be the values of accepted length-t suffixes starting at q, within [0,2^t). Write p=2^t. For t>=3 all of S,2,3,4,5 have nonempty A_q(t). The following table gives (minimum,maximum,count), with E meaning t even and O meaning t odd:

|q|E|O|
|---|---|---|
|S|(1,p-3,F_(t+1)-1)|(1,p-1,F_(t+1))|
|2|(1,p-1,F_t+1)|(5,p-3,F_t-1)|
|3|(5,p/2-3,F_(t-1)-1)|(1,p-1,F_(t-1)+1)|
|4|(1,p-3,F_t)|(5,p-1,F_t)|
|5|(1,p-3,F_t)|(5,p-3,F_t-1)|
|6|(p-1,p-1,1)|empty|
|7|empty|(p-1,p-1,1)|
|8|empty|empty|

Here is a direct induction proof, rather than an extrapolation from a prefix. For q with children r,s, the disjoint ordered union recurrence is

    A_q(t+1)=A_r(t) union (2^t+A_s(t)).

Counts add; minimum is the left minimum unless the left block is empty; maximum is 2^t plus the right maximum unless the right block is empty. At t=3 the sets for S,2,3,4,5,6,7,8 are respectively {1,5,7},{5},{1,7},{5,7},{5},empty,{7},empty. These give the O column. Substituting that column in the eight listed transitions gives the E column at t+1; substituting E gives O. For counts the only identity required in either substitution is F_(t+1)=F_t+F_(t-1). For example q3 uses children5,6: odd t has maximum p-3 and no right block, giving maximum p-3=(2p)/2-3 at the next even level; even t has a right singleton with maximum p-1, giving 2p-1 at the next odd level. qS uses S,2, with minimum1; q2 uses3,4; q4 uses3,2; q5 uses3,5; q6 and7 use8,7 and8,6. These substitutions prove every entry for all t>=3.

Now sigma^3(S)=S2345632. Therefore the accepted positions in the eight consecutive intervals of length p below8p have state blocks S,2,3,4,5,6,3,2. Up to5p the last one is

    A=5p-3.

Within any one nonempty block the distance between successive accepted positions is at most p-1. Across the first five blocks, the four boundary distances are, for odd t, (6,4,6,6), and for even t, (4,6,p/2+4,4). All are <=p for t>=3 (the even case starts at t=4). Thus every consecutive a-distance whose start precedes A is <=p. These blocks start with a_0=1 and cover the entire preceding interval; there is no omitted leading boundary.

After A the next accepted position is B=6p-1 for even t, or B=6p+1 for odd t: state6 is respectively its final singleton or empty, and the next state3 has minimum1 in the odd case. Hence B-A is p+2 or p+4. Summing the counts of the first five blocks gives 2F_(t+2)-1 in both parities. Since A is their last element, its rank is

    J=2F_(t+2)-2.

Consequently the FIRST consecutive c-distance strictly greater than p occurs at

    C_t=c_J=5*2^t-2F_(t+2)-2,
    c_(J+1)-c_J=2^t+1 (t even), or 2^t+3 (t odd).

Every earlier c-distance is <=p-1. In particular each C_t is a strict record location. This proof does not need an exhaustive classification of any additional records between these thresholds. It proves the exact first-threshold property needed below, for every t>=3, including the initial odd boundary t=3.

## 3. Automaticity implies an impossible synchronized graph

Assume g is 2-automatic. Let E(x) mean g_x=2. This is a recognizable predicate. Define

    Next(x,y): E(x) and E(y) and x<y and
               not exists z (E(z) and x<z<y).
    Large(p,x): exists y (Next(x,y) and y>x+p).
    First(p,x): Large(p,x) and
                not exists z (z<x and Large(p,z)).

All are first-order formulas using addition, order and E. Their binary synchronized representations are regular: addition/order are regular, conjunction/complement preserve regularity, and existential quantification is projection followed by normalization of zero padding. Universal quantification follows by complement. This construction is recalled explicitly in Charlier–Rampersad–Shallit arXiv1102.3698v2, Section2, pp3–4 (not an inference from mere decidability). Reversal converts their LSD-first convention into the MSB-first convention here.

Intersect the first coordinate with the regular language 10^t, t>=3. By Section2, First(2^t,x) holds uniquely for x=C_t. The following relation is therefore synchronized regular:

    R(p,d): p=2^t,t>=3, and exists x
            (First(p,x) and x+d+2=5p).

Its exact graph is R={(2^t,2F_(t+2)):t>=3}. Multiplication by the fixed constant5 is repeated addition. No variable exponentiation was used inside a first-order formula: the powers-of-two restriction was imposed by a regular-language intersection.

We prove directly that this graph is not regular. Put d_t=2F_(t+2). The numbers d_t are strictly increasing. Also d_t/2^t tends0: for example F_n<=phi^(n-1), phi=(1+sqrt5)/2<2, by induction. Therefore the difference between the bitlength of2^t and that of d_t tends infinity. For large t, pad the shorter output to the input length t+1. The synchronized word begins with (1,0) followed by an arbitrarily long run of (0,0), before the first output1. In a DFA with Q states choose such a run longer than Q. Two states along this run coincide. Pump that nonempty segment once, leaving the entire suffix unchanged. The accepted word now represents (2^(t+r),d_t) for some r>0. Its first coordinate is still canonical and its second is still correctly padded to the same length. But R requires its second coordinate to be d_(t+r)>d_t, contradiction. Thus g is not 2-automatic. This is an infinite pumping obstruction, not finite kernel growth.

The argument is a synchronized-graph argument with injective output; it makes no false assertion that regular languages cannot have Fibonacci counting functions. It supplies the needed pumping lemma directly, so no unverified structural classification of slender regular languages is invoked.

## 3A. Complete gap structure and records


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

## 4. From arbitrary-base automaticity to recognizable records

Suppose g is k-automatic for any integer k>=2, and put E(x) iff g_x=2. Define Next(x,y) exactly as in Section 3, now in base k. Define

    Gap(x,d): exists y (Next(x,y) and y=x+d).
    Record(x,d): Gap(x,d) and
        not exists z,e (z<x and Gap(z,e) and e>=d).
    V(d): d>5 and exists x Record(x,d).

These are first-order predicates over (N,+,<,E); no powers predicate is present. Record compares EVERY earlier consecutive gap, including earlier gaps ending after the current starting point if such existed; Next makes the definition unambiguous. It is the strict record predicate, so equal earlier gaps prevent another record.

For completeness, the regular-language closure here works in every base. Encode tuples LSD first, padding all coordinates to a common length and permitting arbitrarily many final all-zero columns. Addition is recognized by a finite carry automaton with initial and final carry zero, order by finite comparison, and E by reversal of its canonical DFA plus padding normalization. Boolean operations are taken relative to the universe of padded tuples representing nonnegative integers; use complete DFAs for complement. For existential elimination, project away the witness track, obtaining a regular language K. A witness might require more digits than the visible coordinates. Hence replace K by (K / Z*) Z*, where Z is the all-zero column in the remaining tracks and / is right quotient. This both deletes excess padding needed only for the witness and permits all further padding. Intersect with the nonempty tuple universe (or include the empty all-zero encoding consistently) after each operation. Right quotient by a regular language is regular, as seen by marking states from which some word of that language reaches a final state. This gives exactly all padded representations of the quantified relation, including witnesses of arbitrary length. Reversal gives MSB representations; regular canonical intersection then gives k-recognizability of the value set V. This is also the automaton construction in Charlier–Rampersad–Shallit Section 2, rather than an inference from decidability alone.

By the complete gap classification above, V={D_t:t>=3}. The Presburger filter d=4q+1 selects precisely the even t>=4: even t gives D_t=2^t+1 congruent 1 mod 4, odd t>=3 gives congruence 3. The translation

    P(n): exists d (V(d) and exists q (d=4q+1) and d=n+1)

therefore defines exactly {4^m:m>=2}. It uses only multiplication by the FIXED constant 4, expressed by repeated addition. There is no external predicate for powers of two in base k. Finite initial exceptions could equally be removed by a fixed cutoff, but none occur with this d>5 definition. Thus P is k-recognizable.

## 5. Elementary dependence lemma


Lemma. Fix integers k>=2 and M>=0. If the set {4^m:m>=M} has a regular language of canonical base-k representations, then k^r=4^s for some positive integers r,s. The same conclusion holds if a recognizable set differs from these powers by finitely many integers: remove the finite exceptions and all powers below a sufficiently large bound first, using regular finite-set Boolean closure.

Proof. Let a DFA for the exact canonical language have Q states. Choose a member w of length at least Q+1; this is possible because the set is unbounded. Among the Q+1 states after the first 1,...,Q+1 digits, two are equal. Thus w=xyz, where x is NONEMPTY, y is nonempty, and the state after x equals that after xy. The words xy^j z are accepted for all integers j>=0. Every such word begins with the same nonzero first digit of x, so it is canonical even when j=0; no leading-zero convention is being smuggled into pumping. Its length is nonzero. There is no requirement that z be nonempty.

Put r=|y|>0, h=|z|>=0, X=[x]_k>0, Y=[y]_k>=0, Z=[z]_k>=0. By positional evaluation,

    N_j=[xy^j z]_k
       = X k^(rj+h) + Y k^h (k^(rj)-1)/(k^r-1) + Z
       = A k^(rj) + B,
    A=k^h (X+Y/(k^r-1))>0,
    B=Z-k^h Y/(k^r-1).

The formula holds also at j=0 and when y consists entirely of zeroes. In particular N_j is strictly increasing and unbounded. Since all words are accepted, N_j=4^(m_j) with m_j>=M, and m_(j+1)>m_j. Thus N_(j+1)/N_j=4^(s_j) with s_j a positive integer. The displayed affine-exponential formula gives convergence of these ratios to k^r. A convergent sequence in {4,16,64,...} is eventually constant: it is eventually bounded, hence lies in a finite set, and a sufficiently small neighborhood of its limit contains at most one point of that set. Consequently its limit is 4^s for a positive integer s and k^r=4^s. This proof also rules out k^r<4 directly. No irrational-logarithm, S-unit, Cobham or substitution theorem is used.

Finally k^r=2^(2s) forces k=2^h with integer h>=1 by prime factorization: any prime dividing k divides 2. This is the only arithmetic dependence conclusion needed below. QED.

## 6. All-base endpoint, without Durand

The elementary lemma applied to P shows k=2^h for some h>=1. A k-automatic g would then be 2-automatic. Here is the finite-language base conversion: for each output letter, take its regular language of canonical base-2^h integers and replace every digit by its h-bit binary block (a fixed word homomorphism). This regular image represents the same integers with fewer than h extra initial zeros. Take left quotient by 0* and intersect with canonical binary words; handle index zero separately as a singleton. These regular languages for the output fibers give a binary DFAO, contradicting Section 3. Equivalently this is the published Proposition 3 base-power equivalence. No general Cobham theorem is needed for this step.

Finally assume that the ZERO enumeration b were k-regular over Z for some integer k>=2. Published Proposition 3 gives regularity of its first difference g, and finite-valued k-regular sequences are k-automatic. The difference takes only values 1 and 2 by Section 1. The contradiction just established excludes this possibility for every k>=2. Thus b is not k-regular for any integer k>=2, the full negative answer to Problem 27. QED (ordinary proof proposed; independent review of this revision pending).

The accepted-for-mathematics r242/Durand route is preserved verbatim at frozen/00-PROOF.md and in its untouched original lane. This revision uses neither Durand/nonprimitive substitutions nor any S-unit theorem. Its ordinary source dependencies remain Table 1 and Proposition 3 (plus Proposition 10 for indexing checks); the synchronized construction is proved explicitly and corroborated by the cited primary logic body. No Lean endpoint, novelty clearance or new credit is asserted.
