# Ordinary solution proposed; HOLD pending independent review

Claim. The increasing enumeration b of the zero positions of the compositional inverse of the period-doubling word is not k-regular over Z for any integer k>=2. This answers Rampersad–Stipulanti, JIS21 (2018), Article18.9.1, Problem27 negatively. No literature-priority or campaign acceptance claim is made.

All indices start at zero; F_0=0,F_1=1. The scientific sources and exact copied hashes are in bindings.json. Source Table1 and Propositions3,10,16 are used as published results. The new argument is the first-threshold endpoint calculation and the synchronized pumping contradiction below.

## 1. Exact coding and compression

Let u be the inverse word, a_j its increasing one positions, b_j its increasing zero positions. Table1 accepts canonical MSB-first binary representations of a_j, with states2,6 final. Its transitions on0,1 are 1:82,2:34,3:56,4:32,5:35,6:87,7:86,8:88. Replace initial1 by S with transitions S:S2. Reading leading zeroes in S has no effect. Thus the 2-uniform fixed point w of

    S->S2,2->34,3->56,4->32,5->35,6->87,7->86,8->88

codes u under final-state indicator {2,6}. This also confirms the literal language {11}*1 union 1{1,00}*0{11}*1 in Proposition15. In particular all a_j are odd, and even positions of u are zero.

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

## 4. Every base and the original question

The published Proposition3 implies: if b is k-regular, its difference g is k-regular, and a finite-valued k-regular sequence is k-automatic. When k=2^r, standard base-power equivalence makes g 2-automatic, contradicting Section3. Conversely a 2-automatic g would have 2-regular partial sums b (b_0=0), verifying the r240 yes/no reduction independently.

If k is not a power of2, integers2,k are multiplicatively independent Perron numbers. The word w is purely2-substitutive in the exact sense of Durand1010.4009v1 Definition2: every one of the eight letters occurs (already reachable from S), the substitution is prolongable on S, and its uniform incidence matrix has dominant eigenvalue2. H is nonerasing. A k-automatic g is a coding of a k-uniform fixed point; discard unreachable states, so every retained letter occurs and the dominant eigenvalue is k. Its coding is nonerasing as well. Durand Theorem16, p11, applies to these two nonerasing morphic images without a primitivity hypothesis, and would make g ultimately periodic.

But Proposition16, or the count table above, gives only O(phi^m) ones of u below2^m. Thus a has density0 and is infinite; infinitude also follows from the accepted words 1^(2r+1). Since j/a_j tends0, c_j=a_j-j-1 is an infinite density-zero set too. An infinite ultimately periodic set has positive density, so its indicator, and hence g, is not ultimately periodic. This contradicts Durand and excludes every remaining k. Therefore b is not k-regular for any k>=2. QED (ordinary proof proposed, independently unreviewed).
