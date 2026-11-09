# PART B — MathDB 342017 (Conjecture 1.4 of arXiv 1903.01398v1)

Literal: |SArith(P_{m,n})| "grows at the same rate as" binom(m+n−1,n). Source context: for fixed m, growth in n of a polynomial of degree m−1.

Let N(m,n)=|SArith(P_{m,n})|.

**Theorem B.** Put α_k=(15/4)(5/2)^k+(1/4)(−1/2)^k. For every fixed m≥1, for n large N(m,n) is a quasi-polynomial in n of period dividing 4 and degree exactly m−1, with leading coefficient α_{m−1}/(m−1)!, the same on each residue class. Hence N(m,n)/binom(m+n−1,n) → α_{m−1} as n→∞. Moreover Σ N(m,n)x^{m−1}y^{n−1} is the explicit rational function of §B4.

Remark (scope). N(m,n)=N(n,m), so with n fixed and m→∞ the source formula at n=2 gives N(m,2)~(37/4)m while binom(m+1,2)~m²/2. A uniform two-variable reading of "same rate" is therefore false; the only tenable reading is fixed m, n→∞, as the source's evidence indicates. Root should decide whether this reading binds.

## B1. Reduction to Stern–Brocot words
Definition 1.1/1.3 of the source. Let S be a smooth structure. As in the source, a_{i+1}=(−a_{i−1}) mod a_i and a_2=(−2b_1) mod a_1, likewise for b. So S is determined by (a_1,b_1), with m=F(2b_1,a_1)−1, n=F(2a_1,b_1)−1, F the source's Definition 2.5.
gcd(a_1,b_1)=1: a prime p dividing both divides a_2 (p|a_1 and p|2b_1), inductively every a_i and b_i, contradiction. Conversely every coprime positive pair yields exactly one smooth structure.
F recursion, for positive integers: y>x ⇒ F(x,y)=1+F(x,y−x); x>y ⇒ F(x,y)=F(x−y,y); F(x,x)=2. (Sequence comparison; e.g. y>x gives sequence x,y,y−x,… with x_4≡−x mod (y−x), which is the shifted sequence for (x,y−x).)
For ρ∈Q_{>0} let w(ρ)∈{L,R}* be the subtractive-Euclid word (R if p>q, L if p<q), and S_R=[[1,1],[0,1]], S_L=[[1,0],[1,1]]; then S_{w(ρ)}(1,1)^T=(p,q)^T and w is a bijection. With λ=#L: F(x,y)=λ(x/y)+2. Therefore
  N(m,n) = #{ρ∈Q_{>0}: λ(2ρ)=m−1, λ(2/ρ)=n−1},  ρ=b_1/a_1. (1)
Also w(1/ρ) is w(ρ) with L↔R.

## B2. Doubling transducer (Raney-type, verified by 2×2 multiplication)
D=diag(2,1), H=diag(1,2), E=[[2,0],[1,1]], E'=[[1,1],[0,2]]. Identities:
D·R=RR·D, D·L=E, E·R=R L·H, E·L=L·D, H·L=LL·H, H·R=E', E'·R=R·H, E'·L=L R·D.
Terminals: D(1,1)=R(1,1), H(1,1)=L(1,1), E(1,1)=E'(1,1)=2(1,1). Hence w(2ρ) is the output of reading w(ρ) from D, with terminal R, L, empty, empty.

## B3. Ten-state automaton
Run machine A on w(ρ) (weight x per output L, giving m−1) and machine B on the swapped word (weight y, giving n−1). Reachable joint states, each row "letter → next(weight)", terminal weight in brackets:
S=(D,D)[1]: R→P(1), L→Q(1). P=(D,E)[1]: R→S(y), L→P'(y). Q=(E,D)[1]: L→S(x), R→Q'(x).
P'=(E,H)[y]: R→T(xy²), L→U(x). Q'=(H,E)[x]: L→T(x²y), R→V(y). T=(H,H)[xy]: R→W(y²), L→X(x²).
U=(D,E')[1]: R→S(y), L→P'(1). V=(E',D)[1]: L→S(x), R→Q'(1). W=(E',H)[y]: R→T(y²), L→U(x). X=(H,E')[x]: L→T(x²), R→V(y).
No cycle has weight 1, so the series below are well defined in Z[[x,y]].

## B4. Series
Writing a,p,q,p',q',t,u,v,w,z for the generating functions at the states, the system reduces to
 a(1−x−y)=3+y p'+x q'; p'(1−x)=y+x+xya+xy²t; q'(1−y)=x+y+xya+x²yt;
 t(1−x⁴−y⁴)=xy+x³+y³+xy²u+x²yv, u=1+ya+p', v=1+xa+q'.
Then a=Σ N(m,n)x^{m−1}y^{n−1}. Exact low orders: a_0=(3+y²)/(1−y); a_1=y⁶/((1−y)(1−y⁴))+(3+2y+4y²−y³+y⁴)/(1−y)²; a_2=(4+9y+18y²+16y³+20y⁴+12y⁵+9y⁶+4y⁷+y⁸+y⁹)/((1−y)²(1−y⁴)).

## B5. Pole analysis (proves Theorem B)
Let f_k=[x^k]f. From §B4, with [k=j] Iverson and terms of negative index 0:
 p'_k=p'_{k−1}+y a_{k−1}+y²t_{k−1}+[k=1], p'_0=y;
 (1−y)q'_k=[k=0]y+[k=1]+y a_{k−1}+y t_{k−2};
 (1−y⁴)t_k=[k=0]y³+[k=1](y+y²)+[k=2]y+[k=3]+t_{k−4}+y³a_{k−1}+y²p'_{k−1}+y a_{k−3}+y q'_{k−2};
 (1−y)a_k=3[k=0]+a_{k−1}+y p'_k+q'_{k−1}.
At y=1, by induction, ord a_k,q'_k,t_k ≤k+1 and ord p'_k≤k, with leading coefficients α_k=lim(1−y)^{k+1}a_k, κ_k, τ_k, π_k:
π_k=α_{k−1}+τ_{k−1}, κ_k=α_{k−1}, τ_k=α_{k−1}/4 (k≥1; note 1−y⁴~4(1−y)), α_k=2α_{k−1}+τ_{k−1}+κ_{k−1}, α_0=4, κ_0=1, τ_0=1/4.
So α_1=37/4 and α_k=2α_{k−1}+(5/4)α_{k−2} (k≥2), giving the closed form, α_k>0.
At ζ∈{−1,±i}: by induction ord_ζ(a_k,q'_k,p'_k)≤⌈k/2⌉ and ord_ζ t_k≤⌊k/2⌋+1, strictly below k+1 for all k≥0.
Partial fractions give the stated quasi-polynomial and leading coefficient α_{m−1}/(m−1)!. ∎

## B6. Agreement with the source and one source error
a_0 gives 3,3,4,4,… (source Thm 3.1). a_1 gives exactly 9n−11+⌊(n−3)/4⌋ for n≥4 and 3,8,17 (source Thm 4.2/Table 1, entries through n=15 compared).
a_2 has leading coefficient 47/4 (source Thm 5.3). For m=3 the series differs from source Theorem 5.3/Table 3 by exactly y⁴/(1−y²), i.e. the source count is too small by 1 for odd n≥5.
Located cause: in source Table 2 row "k≡0, t≡2", the uniform equation n−6=(k−4)/4+4(ℓ−2)+(t−2)/4 fails at t=2, where F(4a,4a−2)=4ℓ−2 gives n−5; similarly t=3 in row t≡3 gives n−7, not n−8. The two shifts contribute y⁴(1+y²)/(1−y⁴)=y⁴/(1−y²).
Hand-checked witness: (a_3,a_2,a_1;b_1,…,b_5)=(1,2,3;5,4,3,2,1) is smooth on P_{3,5}: 1|2, 2|1+3, 3|2+10, 5|4+6, 4|5+3, 3|4+2, 2|3+1, 1|2. Source row places this at n=6. (No credit claimed for this correction; Table 3 was not brute-force compared because this lane cannot run enumeration.)

## B7. Adversarial self-review (mandatory)
Generic-proof attempts: (1) Direct bounds from Lemma 2.7/2.8: for fixed m, c_i-run parameters give λ(4/σ) piecewise linear on mod-4 classes, which gives Θ(n^{m−1}) in principle, but carrying this through for general m requires a state summary equivalent to §B3. A critic may fairly say the Θ reading alone is an iterated version of the source's mod-4 casework. (2) A one-parameter family containing the target: none found. (3) Reduction to a known theorem: Raney's transducers are classical input; what is new is the two-machine coupling via (1), the 10-state system and the eigenvalue 5/2 constant.
Honest risk: routine-extension objection to the Θ reading; the exact rational GF, the constant α_{m−1} and the correction of Theorem 5.3 go beyond it. "Same rate" is informal, so the literal binding needs root's ruling.
Prior art: one bounded search; Keyes–Reiter 2007.15100v2 read for its mention only (statement only, no proof); Integers 20 (2020) A68 final NOT read. core.ac.uk/download/345953608.pdf, observed in search, returned HTTP 403, identity unread: treat as a specific unread HOLD (if it is the final, no alternate delivery may be sought). No worldwide novelty claim.
