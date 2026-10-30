# Candidate: an exact counterexample to Kovalev's trigonometric positivity conjecture

Strict discovery credit: **pending; not assigned by this lane**. Exact mathematical counterexample and kernel-checked arithmetic complete. The parent and matrix lanes supply the full source-coefficient/cosine bridge. Latest published-body comparison remains a material novelty-review gap.

## Exact claim refuted

Leonid V. Kovalev, *Sharp bounds for some segments of bounded power series*, arXiv:2507.04544v1, Conjecture1.3, proposes that for every integer d≥2, every n≥0, and every real t,

\[
 \mathcal T_n^{(d)}(t)=\sum_{k=0}^n b_k^{(d)}\cos(kt)>0,
 \qquad \sqrt{1+z+\cdots+z^d}=\sum_{k\ge0}b_k^{(d)}z^k,
\]

where the square-root branch has constant term1. Exact primary source: <https://arxiv.org/html/2507.04544v1>. MathDB369172 records this conjecture.

The explicit counterexample is

\[
 \boxed{d=49,\quad n=949,\quad t=\arccos(523/527).}
\]

Its exact value is negative; a decimal approximation, used only for orientation, is

\[
 \mathcal T_{949}^{(49)}(\arccos(523/527))\approx-0.000475321859370024.
\]

This refutes Conjecture1.3. It does not prove or refute the separate zero-free Taylor-polynomial Conjecture1.2/MathDB369171: a negative real part at a point does not itself produce a polynomial zero.

## Exact coefficient specification

Put D=d+1=50 and define c_k=binom(2k,k)/4^k. Let u_0=1 and

\[
 u_j=\frac{2j-3}{2j}u_{j-1}\quad(j\ge1).
\]

Thus u_j is the coefficient of z^j in sqrt(1−z). Coefficients of the normalized square root are

\[
 b_k=\sum_{j=0}^{\lfloor k/50\rfloor}u_j c_{k-50j}.
\]

This follows by multiplying sqrt(1−z^50) and (1−z)^(-1/2); both have constant term1 and their product squares to(1−z^50)/(1−z). Define the exact integers B_k=4^k b_k. The generator verifies their integrality before using any integer truncation.

For an independent, linear-size coefficient certificate, let F(z)=Σb_kz^k. Logarithmic differentiation of its defining equation gives

\[
 2(1-z)(1-z^{50})F'
 =[1+49z^{50}-50z^{49}]F.
\]

Comparing coefficient z^(k−1), for k≥1, gives the **corrected** recurrence

\[
\begin{aligned}
 2k b_k={}&(2k-1)b_{k-1}
 +\mathbf1_{k\ge50}(2k-150)b_{k-50}\\
 &-\mathbf1_{k\ge51}(2k-151)b_{k-51}.
\end{aligned}
\]

Together with b_0=1 this determines every coefficient uniquely. Scaling by4^k gives the integer identities checked for all1≤k≤949:

\[
\begin{aligned}
 2k B_k={}&4(2k-1)B_{k-1}
 +\mathbf1_{k\ge50}4^{50}(2k-150)B_{k-50}\\
 &-\mathbf1_{k\ge51}4^{51}(2k-151)B_{k-51}.
\end{aligned}
\]

An early draft incorrectly used2k−53 in the last term. Exact recurrence validation caught that error before the Lean certificate was generated. The frozen certificate and all formulas here use2k−151. The original coefficient formula and negative evaluation were unaffected.

## Exact cosine and sign certificate

Define integers C_0=1, C_1=523, and

\[
 C_k=1046C_{k-1}-277729C_{k-2}\quad(k\ge2).
\]

The elementary cosine recurrence, with cos(t)=523/527, proves

\[
 C_k=527^k\cos(kt).
\]

Define H_0=0 and H_(k+1)=2108H_k+B_kC_k for0≤k≤949. Induction gives

\[
 H_{950}=\sum_{k=0}^{949}B_kC_k2108^{949-k},\qquad
 \mathcal T_{949}^{(49)}(t)=\frac{H_{950}}{2108^{949}}.
\]

The denominator is positive. The exact integer H_950 is negative; its full3152-digit decimal representation is retained in `TRIG-EXACT-NUMERATOR.txt` and `trig-integer-sign.json`, rather than replaced by floating-point evidence. The latter also records the full reduced rational value. Direct exact arithmetic additionally shows H_950/2108^949<−1/2500; this extra margin is not needed by the Lean contradiction and is not advertised as a separate formal endpoint.

## Formal certificate and independent arithmetic

- `formal/TrigCertificate.lean` contains the exact B/C data using balanced binary lookup, the complete finite recurrence checks, and H_950<0. All checks use ordinary kernel-checked `decide`, with no native_decide or new axioms.
- `formal/TrigArithmetic.lean` exposes the recurrences, rational normalized coefficients, Horner induction, and negative weighted numerator. Both frozen modules compile with the pinned Lean4.34.1 and warnings as errors.
- `make_trig_certificate.py` regenerates the frozen integer certificate **byte for byte**. It first computes B from the exact square-root product formula, then independently checks every displayed integer recurrence before emitting Lean.
- `exact_trig.py` separately evaluates the rational Chebyshev sum and checks all defining square-convolution identities through degree949.
- The matrix reviewer independently generated B from the defining square-convolution recurrence rather than the product formula, and independently confirmed the negative integer Horner value. Its independent files are under `lanes/matrix/trig-positivity-review/`.

Axiom inspection: the C recurrence check and negative Horner check use no axioms; the B recurrence check uses propext only. The normalized rational and finite-sum algebra use only propext, Classical.choice, and Quot.sound.

The parent formal bridge proves H_950=2108^949 times the actual cosine sum. The matrix formal source bridge proves existence and uniqueness of the canonical normalized square root and the source coefficient recurrence. Final integration of these independent modules is managed by the parent.

## Source and novelty limits

The exact arXivv1 text states the conjecture. Its current abstract page lists Arkiv för Matematik64(2)(2026),273–282, DOI10.4310/ARKIV.2026.v64.n2.a4. The live record still has onlyv1, but the actual publisher body has not yet been compared: the public publisher requests returned403, and two standard legacy full-text paths returned404. Targeted title, conjecture, and parameter searches found no prior disproof. These searches are evidence of investigation, not proof of universal absence. Final discovery credit awaits independent novelty assessment including the latest published version.

The discarded coarse rational approximation cos(t)=131/132 was positive and is not a counterexample. All retained exact negative artifacts use523/527.

## SHA256 manifest

- `sources/2507.04544v1.html`: `8b045995bf566ec75736dba0d01d0259ae1c5541a9fb3d3c643de92152ad9e47`
- `sources/369172.json`: `95e36bf7a80095fcc40e70616795b103f35fc201910ad18b9e92cf69e1006d0f`
- `trig-exact-certificate.json`: `b27d20cee328c329f4318a8d509762d2585671f938a210ef7d2b609f2b7f605f`
- `trig-integer-sign.json`: `77c863e837a12f625d2d9bf0f369b8be2359ab12517a391557ef060c8c055c88`
- `TRIG-EXACT-NUMERATOR.txt`: `f6c01eb392fbc5ca3510694dd298dc26d2c55c669103a3b137d494a86263ca23`
- `make_trig_certificate.py`: `19c7e046b45c60ee6496b9b369099281e5d2b6dc9a6d75eb513f8ff22fd56920`
- `formal/TrigCertificate.lean`: `86cd4e317fcf9909f4fcef4a0295b396840bb7724033c69195e7bf5b6190b0a3`
- `formal/TrigArithmetic.lean`: `d1b4bba64da2f65a5a8497a9cc3090813cb7ba6ae533789042934a6bc8f7fae4`
