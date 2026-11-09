# Round 5B proof

The frozen round-4 packet supplies Lemma R, Lemma W, the readouts and strict
positivity. All of its 21 modules are imported unchanged.

The half-angle pair starts with A_0=B_0=1 and satisfies
A_(h+1)=A_h+4Y B_h and B_(h+1)=A_h+(1+4Y)B_h.
It represents w^h(1+y) by the parity numerators (1+Y)A_h and 2B_h-A_h.
Both polynomials have coefficients divisible by 4^E. The polynomial Pell
identity (1+Y)A_h^2-Y(2B_h-A_h)^2=1, proved by this recurrence, gives
sectionEven(w^(2h+1))+1=2(1+y)ev(A_h^2).

The identity y^2=w expand_2(y) gives the half-angle rules:
T'(Y^(2e))=Y^e A_(m+e), and
T'(Y^(2e+1))=2Y^(e+1)B_(m+e).
The operator preserves coefficient divisibility by 4^E. Its constant coefficient
is unchanged. Thus (T'-1)G=YQ with G=A_h^2, and R=2Q is a genuine initial
reduced representative of the actual transfer difference for m=2h+1.
Every R_F is divisible by 2^(2F+3).

For completeness the universal frozen polynomial is also factored directly:
polyEven preserves evaluation at 0 and -1, so polyIter(m,2)-1 is divisible
by Y(1+Y). No series-to-polynomial or interpolation premise is used.

The defining series functional equation computes coefficients C_0 through C_12.
Multiplication induction proves n![x^n]C^m as a polynomial in m for n≤12.
The actual readout at n=2 and n=3 identifies R_1 and R_2, using the frozen
constant identity 3R_0=2m^2(m+1)(m+5). This gives exactly the review's
numerators with odd denominators 315 and 467775. Explicit ring identities
on each residue class give the divisibility estimates and the exact valuation
7 of R_1 when m=16t+11. There is no degree bound or interpolation argument.

For m=4k+1, the crude bound gives weight at least 3, while the constant is
not divisible by 16. The frozen readouts give OddOneBound and OddOneEquality.
For m=4k+3, the constant is divisible by 64 and R_1,R_2 by 128. The initial
polynomial is divisible by 64 and has weight at least 5. Its reduced main
part has weight 7, as does its tail by frozen Lemma W. This supplies the
bound for positive halving indices; the initial divisibility covers index zero.
For m=16t+15 the constant is divisible by 128, R_1,R_2 by 2048, and the
crude estimate gives initial weight 7, proving FifteenBound directly.

For m≡3 or 7 mod 16 the initial constant is exactly divisible by 64,
and every higher coefficient is divisible by 128. For m≡11 mod 16 the
next constant is 2(m+1)R_0+R_1: its first term is divisible by 256 and
R_1 is not; the reduced polynomial has weight 7. The exact odd readout
therefore proves equality at odd n in the first two classes and n≡2 mod 4
in the third. These are sufficient sets, as required; no converse is claimed.

Review fixes: transfer integrality is proved; no inconsistent 4F+4/4F+5
degree estimate is needed; the line-150 bound needed for the fifteen family
is at least 8, not 11, and the stronger actual low-coefficient bound 11 is
proved here. No numerical evidence is used as a proof.
