# Round 4 proof status

This is a partial formalization, not an accepted resolution. All six endpoint
Props remain open. The round-3 sources are frozen and included unchanged.

## New proof of Lemma R

Let y = X geomStep(1). The identities 1+y = geomStep(1), X(1+y)=y,
and y = expand₂(y) + X expand₂(1+y) hold over integer series.
Represent a series by a polynomial pair (a,b) through
f = expand₂(ev a) + X expand₂((1+y)ev b).
Multiplication by y transforms the pair into
(Y a + Y(1+Y)b, a+Y b). This proves a polynomial even-section
operator for all integer polynomials, with no degree restriction.

For w^m y(1+y)y^E factor Y(1+Y) from the even numerator.
The reduced pair starts at (2,1+2Y). Multiplication by y gives
(r,b) -> (Y r+b, Y(1+Y)r+Y b), and multiplication by w gives
(r,b) -> ((1+2Y)r+2b, 2Y(1+Y)r+(1+2Y)b).
Two y steps equal one w step and an output factor Y.

Define A_m = sum_i 2^(2i+1) choose(m+i+1,2i+1)Y^i and
B_m = sum_i 2^(2i) choose(m+i+1,2i)Y^i, with cutoff m+2.
Outside that cutoff the binomial coefficients vanish. Pascal gives
A_(m+1)=A_m+2B_m and B_(m+1)=B_m+2Y A_(m+1).
Together with A_0=2 and B_0=1+4Y these identify the reduced pair:
r_(m,2e)=Y^e A_(m+e), r_(m,2e+1)=Y^e B_(m+e).
Linearity proves equality with the exact frozen Round3.reduced, including
its cutoffs. Thus Lemma R is unconditional, not an additional hypothesis.

## Readout and nonzero differences

The frozen general-j readout and Lemma R give an iterated reduced polynomial
representative from any genuine initial representative. Lemma W now proves
divisibility of the actual differences by 2^(v+j).
The exact odd-index readout uses C^m = 1 modulo two and
[x^n]y(1+y)=n. If R_0 is exactly divisible by 2^a and all positive
coefficients by 2^(a+1), the odd-index readout has valuation exactly a.

All coefficients of C are positive, by the finite product definition.
The functional equation gives (1-X)C=(1+X)expand₂(C); the right side has
positive coefficients. Multiplying by C^m proves strict increase of c_(m+1).
Consequently diff m n > 0 for every m,n ≥ 1, independently of initialization.

## Even invariant

EvenInvariant(v,R) states Weighted(v,R), nondivisibility of R_0 by 2^(v+1),
and divisibility of R_(2^i-1) by 2^(v+i+1) for i≥1.
The exact reduced constant formula and the oddness of m+1 preserve the
constant valuation. The main/tail coefficient decomposition and stronger
Lemma W tail gain preserve the exceptional coefficients. Hence reduced
preserves the invariant with v increased by one for even m. Its iteration
and exact readout prove EvenFormula from EvenInitialization alone.
The needed initialization is NOT proved.

The universal initial constant satisfies 3 R_0 = 2m^2(m+1)(m+5)
whenever R is a genuine initial reduced representative. The odd initial
representative, higher low coefficients and bounds are still missing.

## Review corrections retained

The operator integrality issue is now proved, not merely stated. The odd
coefficient polynomial degree estimate must use 4F+4 or the safe 4F+5,
not an inconsistent smaller bound. The review's line-150 correction is
valuation at least 8, not 11; 8 is enough at that point. None of the
unformalized interpolation claims is treated as a theorem in this packet.
