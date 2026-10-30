# Exact source coefficient bridge for MathDB369172

These supporting lemmas serve one counterexample to Kovalev's trigonometric-positivity Conjecture1.3; they carry no separate discovery credit. Source/literature review and exact independent witness are in the sibling `trig-positivity-review/` lane. In particular, the current arXiv record's2026 published body remains inaccessible and is not represented as having been read.

All three formal modules use namespace `TrigSource` and import in this order:

1. `SourceCoefficients`: canonical source root, its full defining square, constant term and exact differential identity.
2. `SourceRecurrence`: Euler derivative, corrected coefficient recurrence and finite strong-induction uniqueness.
3. `SourceBridge`: convenient source coefficients, normalized-root uniqueness and source/certificate matching.

## Canonical source definition and uniqueness

For a positive integer D, define G_D(X)=Σ_(j=0..D−1)X^j. Induction gives G_D(1−X)=1−X^D and its constant coefficient is1. Define

    sourceRoot D = binomialSeries(1/2).subst(G_D−1).

Substitution is legitimate because G_D−1 has constant coefficient0. Mathlib's binomial-series addition law gives binomialSeries(1/2)^2=1+X. Applying substitution therefore proves sourceRoot(D)^2=G_D; its constant coefficient is1. This is an unconditional construction, not an assumed square-root existence assertion.

If any formal series B has B²=G_D and constant coefficient1, then B=sourceRoot(D). Indeed (B−sourceRoot)(B+sourceRoot)=0 in the integral domain of real formal series, while B+sourceRoot has constant coefficient2 and cannot vanish. Thus the formal construction selects exactly the normalized square-root coefficients specified in the primary source. Any analytic Taylor expansion of that normalized germ satisfies these same identities and hence has the identical coefficients. The finite counterexample requires no claim about a numerical approximation to the analytic square root.

## Differential and coefficient identities

Differentiate B²(1−X)=1−X^D formally:

    2(1−X)BB'=B²−D X^(D−1).

Multiply by B(1−X), replace B²(1−X) by1−X^D, and rearrange. No division or unsupported cancellation is needed:

    2(1−X)(1−X^D)B'=[1+(D−1)X^D−D X^(D−1)]B.

For E=XB', coefficient k of E equals k b_k. Multiplying the differential identity by X and taking coefficient k yields, for every k≥1,

    2k b_k=(2k−1)b_(k−1)
      +1[k≥D](2k−3D)b_(k−D)
      −1[k≥D+1](2k−3D−1)b_(k−D−1).

The three Lean branches D+1≤k, D≤k<D+1, and k<D justify every natural subtraction/cast, so no negative-index coefficient convention is hidden. The final coefficient is2k−3D−1; the earlier proposed2k−D−3 was an error detected before certificate generation and is not present in these modules.

## Certificate interface

`CoeffRec D a k` names exactly the real recurrence above. `recurrence_unique_upto` proves by strong induction that two sequences with the same index0 value and this recurrence through N agree at every k≤N. D>0 makes all referenced indices smaller than k in each enabled branch, and2k is nonzero.

`sourceCoeff D k` is coefficient k of the canonical source root. Main bridge:

    sourceCoeff_matches (D N : Nat) (hD : 0<D) (a : Nat→Real)
      (ha0 : a0=1)
      (ha : ∀k,1≤k→k≤N→CoeffRec D a k)
      : ∀k,k≤N→sourceCoeff D k=a k.

`rootCoeff_matches` additionally accepts any normalized root B²=G_D and gives the same coefficient agreement. For the proposed witness set D=50,N=949,a(k)=the real cast of the originating worker's exact rational `TrigCertificate.certCoeff k`. The caller discharges ha0 and ha using the frozen numerical module and ordinary rational-to-real casts. This leaves no source-root, recurrence or coefficient-identification hypothesis in the assembled counterexample.

The parent owns the final rational Chebyshev/cosine and real arccos bridge. The originating worker owns the finite exact coefficient/Chebyshev/Horner certificate. These files remain supporting modules and do not alone assert the final trigonometric inequality.
