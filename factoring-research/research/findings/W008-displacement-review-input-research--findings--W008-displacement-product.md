# W008 — two compact factors can destroy the Hankel displacement state

2026-10-08. Parent derivation, PROVISIONAL pending independent audit.
This develops the actual multiplication gate selected in section 9 of
[the four-list review](W008-fourlist-review.md). No candidate run, solver or
Lean change, and no factoring bound.

## Proposed saving and the operation tested

In Q=R[X,Y]/(F_C(X),F_D(Y)), one input factor is
H_b=F_A(X+Y-b). For degree-K monic F_A, its coefficient array C becomes
Hankel after scaling Ctilde_rs=r!s! C_rs, apart from the pure-variable
boundary changes caused by reduction. Consequently
Delta(Ctilde)=J Ctilde-Ctilde J^T, with J the downward shift, has bounded
rank for a single factor. A rank-r generator stored as U V^T uses O(Kr)
entries. The hoped-for computation was to update short generators under
quotient multiplication, then obtain the determinant norm without writing
K^2 coefficients.

Here is an explicit two-factor obstruction to maintaining this same
low-displacement-rank representation. This is not a lower bound for an
implicit formula, a different displacement operator, or the scalar norm.

## Exact family, no search

Take K>=2 over Q and specialize

    F_A(T)=T^K,  b_1=b_2=0,
    F_C(X)=X^K-1,  F_D(Y)=Y^K.

Each factor H=(X+Y)^K mod (X^K-1,Y^K) has the single-factor structure
above. Their product is the residue of (X+Y)^(2K). Its only nonzero
coefficients are

    C_00=1,
    C_(r,K-r)=binom(2K,K+r),  1<=r<=K-1.

Indeed powers of Y at least K vanish. Terms with X exponent K+r,
1<=r<=K-1, reduce to X^r Y^(K-r), while X^(2K) reduces to 1.
The term with X exponent K has Y exponent K and vanishes.

After factorial scaling put

    w_r=(2K)! r!/(K+r)!,  1<=r<=K-1.

Thus Ctilde_00=1 and Ctilde_(r,K-r)=w_r. Its displacement has the
top-left block [[0,-1],[1,0]]. On rows and columns 2,...,K-1 its only
nonzero entries lie on r+s=K+1 and are

    Delta_(r,K+1-r)=w_(r-1)-w_r
                         =K (2K)! (r-1)!/(K+r)! > 0.

The two blocks do not interact. Therefore

    det Delta = (-1)^((K-2)(K-3)/2)
                product_(r=2)^(K-1) [K (2K)! (r-1)!/(K+r)!] != 0.

For K=2 the product is empty and det Delta=1. Hence this displacement
has rank exactly K after only two multiplicative updates. An explicit
rank-factor generator U,V consequently needs quadratic-size arrays.

The specialization F_C=X^K-1 need not split over Q. It is a valid
symbolic quotient-algebra certificate: its nonzero determinant proves
that the determinant polynomial in monic F_A,F_C,F_D and shifts is not
identically zero. Substitution of elementary symmetric polynomials in
formal list roots is injective, so generic split-list inputs also have
full displacement rank. This does not assert a useful probability over
the finite fields at the factoring scale, nor a bound on modular
exceptional characteristics. Repeated A entries and equal shifts in the
certificate are permitted by the original arbitrary-list contract.

## What has and has not been removed

The failed assumption is closure of a single Hankel displacement
description under multiplication after the two quotient reductions.
The input factors individually remain compact. A scheme that explicitly
stores arbitrary K-by-r generator arrays loses the desired saving as
soon as it encounters this family. The special full-rank displacement
above itself has a short anti-diagonal formula, so full rank is emphatically
not a lower bound for every representation or every input-specific program.

Two changed computations are outside the calculation:

1. Keep the product as a list/tree of its original compact factors and
   update the scalar determinant norm without forming their product's
   generator. Norm multiplicativity is an identity, not such an update:
   the cost of computing each factor's norm and sharing those computations
   across all shifts still has to be supplied.
2. Choose a displacement operator adapted to both quotient polynomials
   and retain its generators under multiplication. The usual fact that
   all multiplication matrices commute is insufficient: zero commutator
   does not provide a cheap determinant. Give an explicit norm algorithm
   as well as a closed representation.

Neither change currently has a sub-K^2 algorithm. The next cheap test is
independent symbolic verification of this determinant and its precise
scope. Do not run a factoring screen to test a characteristic-zero identity.
