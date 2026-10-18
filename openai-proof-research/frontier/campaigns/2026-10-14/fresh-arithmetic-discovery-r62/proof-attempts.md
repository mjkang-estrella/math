# T012D62: exact stripping obstructions

Full frozen target unresolved. No partial or conditional nominee. Author: Myeongjin Kang; original prose CC BY 4.0.

## 1. Source interface and the attempted operation

The pinned family012 already proves independence of the entire two-endpoint finite bin-count vectors, not merely two largest prime factors. This was also recorded in I07. It does not give a third endpoint. I18 studies a different target: two neighbors under a prime midpoint condition. Neither changing the number of bins nor repeating the two-endpoint Fourier inversion supplies T012D62.

For fixed J, let g_x,h_x be unit-modulus completely multiplicative bin characters supported on primes above x^(1/J), and let F_x=f_x−mu be a centered such character. All three are invariant under multiplication by any fixed positive integer once x is large. A sufficient new mixed statement is

    x^(-1) sum_{n<x} g_x(n) F_x(n+1) h_x(n+2) → 0,

together with the corresponding centering of the other coordinates, or directly factorization of all three bin-character means. We do not assert that the displayed middle-centering statement alone implies the entire triple law: its uncentered outer term would still need the shift-two pair law. The intended full three-character factorization would imply the frozen theorem by finite Fourier inversion, rational threshold grids, and marginal continuity. That passage is routine, and is not nominated.

The source amplifier is a nonnegative count of n=a m, n+1=c l_a, with a,c from finite sets when B is fixed. The x limit precedes the B limit. Its profile-preservation argument can still begin with the triple product because that product is bounded; the obstruction is later, when labels must pass through Cauchy–Schwarz and the endpoint kernel.

## 2. First attempt: retain the source amplifier

After n=a m, fixed-multiplier invariance removes g_x(a m), leaving g_x(m) outside the inner coefficient sum. The additional label is h_x(a m+2). Cauchy–Schwarz in (c,m) therefore produces, for coefficients a,b with c dividing both a m+1 and b m+1, the exact product

    conjugate(F_x(a m+1)) F_x(b m+1)
      conjugate(h_x(a m+2)) h_x(b m+2).

Write a−b=c j and use the source substitution

    u=b(a m+1)/c,  v=a(b m+1)/c=u+j.

Multiplying the third arguments by the fixed integers b,a respectively gives

    b(a m+2)=c u+b,
    a(b m+2)=c v+a=c u+b+2c j.

Hence the actual label product is exactly

    conjugate(F_x(u)) F_x(v)
      conjugate(h_x(c u+b)) h_x(2c v−c u+b).                 (A)

The variables b,c belong to the divisor representation of the edge (u,v); they are not determined by its two site-prime sets. Even fixing b,c, the last factor is evaluated on the mixed affine form 2c v−c u+b. It is not a column label depending only on v. This is the unpaid operation: the source comparison is a cut-norm comparison tested against a row label times a column label. Its sampling upgrade permits those vectors to depend on the whole sampled configuration; it does not turn an arbitrary function of each ordered edge into a row-column product.

Taking absolute values of the extra factors before graph comparison leaves only a bound by total edge mass. That mass is bounded, not tending to zero. Taking absolute values of the inner coefficient sum earlier likewise loses the centered cancellation. A Fourier decomposition of the mixed affine label into row-column terms would cost its Fourier l1 norm; boundedness alone gives a square-root-of-block-length bound, while the source has only a fixed-accuracy cut estimate followed by B→infinity. No rate that absorbs this growing loss has been proved. No claim is made that arbitrary graph counterexamples are arithmetic bin-label counterexamples.

The exact new estimate would have to control the representation-decorated graph pairing (A), or a stronger linear-forms norm of its kernel, without a loss growing with the shift scale T(B). It cannot be inferred from the printed two-site integral comparison and sampling statements.

## 3. Second attempt: strip both outer labels simultaneously

Try to write

    n=a m,  n+2=d r,

with a,d from finite coefficient sets A_B,D_B, then remove g_x(a m)=g_x(m), h_x(d r)=h_x(r), and apply Cauchy–Schwarz in the pair (m,r). The following exact fact shows why the same fixed-auxiliary-scale method cannot create useful off-diagonal terms.

**Uniqueness lemma.** Fix finite positive coefficient sets A,D, with maxima Amax,Dmax, and eta>0. Suppose eta x≤n≤C x and

    n=a m,  n+2=d r,  a∈A, d∈D.

For x>2 Amax Dmax/eta, the pair (m,r) determines a,d uniquely among all solutions of a m−d r=−2 with a∈A,d∈D.

Proof. Any common divisor of m and r divides 2, so g=gcd(m,r)≤2. For another pair b,e, subtraction gives

    (a−b)m=(d−e)r,

and therefore r/g divides a−b. Since r=(n+2)/d≥eta x/Dmax, we have r/g>Amax. But |a−b|<Amax unless a=b already. Hence a=b, and then d=e. This is an exact arithmetic argument in the actual consecutive-integer configuration, not an abstract model. ∎

At fixed B, Amax,Dmax are fixed. The lemma applies throughout the positive compact scale support used in the source once x is large. One may retain extra divisor coefficients c dividing n+1, but for a fixed residual pair (m,r), the integer n is already unique. Every remaining c term has the same centered label F_x(n+1). Thus the squared inner sum has the form

    |F_x(n+1)|^2 |sum_c w_c(n)|^2,

rather than a product of centered labels at distinct additive endpoints. There is no off-diagonal coefficient graph whose short-shift cancellation can contradict a positive energy. For a nonconstant unit-modulus bin character, the unweighted limiting square mean of F_x is 1−|mu|^2, which is positive; centering is not a reason for this same-point square to vanish.

This defeats this particular simultaneous-stripping arrangement. It does not disprove the triple Dickman target and does not rule out a higher-order amplification with a different set of retained variables.

## 4. Can the coefficient scale escape the uniqueness threshold?

The lemma forces the product Amax Dmax to be comparable to x if one wants distinct bounded-window representations with the same residual pair. This is incompatible with the source's iterated order x→infinity at each fixed B. Choosing B=B(x) is not an authorized substitution into its qualitative o_x(1) estimates.

Exact multiplier invariance alone could survive some growing coefficients if all their prime factors remain below x^(1/J). That observation does not repair the argument. The source's profile test uses finite residue moduli fixed in the inner x limit; growing coefficient supports change those moduli. Its marginal comparison also uses residual sizes equal to a fixed positive multiple of x at fixed B, so log(m)/log(x)→1. If a reaches x^theta, the residual has logarithmic size 1−theta instead. The same bin thresholds then describe a different limiting count region; one cannot use the unchanged mean mu or the same centered short-average statement. New uniform moving-scale arithmetic and a compatible centering calculation would be required.

No such estimate or recentering has been established here. The standard CRT factorial-moment range with total selected logarithmic mass below one gives supporting interior information only and is not a substitute for the full three-coordinate target. It was deliberately not expanded into another routine partial result.

## 5. Final mathematical status

The target remains exactly the all-threshold, all-scale triple Dickman law. The retained calculations identify why both natural divisor arrangements fail to close it: one leaves a mixed affine third label outside the source cut interface, the other has no off-diagonal coefficient pairs at all. A genuinely new representation-decorated graph estimate or a uniformly recentered moving-coefficient construction remains necessary for these approaches. No complete proof or counterexample to T012D62 has been obtained.
