# r51 — source-scope exclusion; no eligible discovery

Credit 0. Root acceptance/counts untouched (6 additional, 36 total). SOLO, assigned-lane writes only. No Lean, paper, git, external messages, browser, uploads or accounts.

## Screen and selection

Three primary leads were screened, with only one selected for sustained mathematics. No fourth question was selected.

1. Krasniqi–Shabani, AJMAA11(1)(2014), Art5, Problem1, p3: find theta(t) making t^[t(psi_q(t)-log theta(t))-gamma] logarithmically completely monotone on all positive t. Actual published full five-page body read. Arbitrary theta permits encoding any desired logarithm through solving for log theta away from t=1; that is a tautological parametrization, not a substantive solution. Do not nominate it. The paper's earlier use of -log t as a nonnegative CM function on all positive t is invalid, but correcting that is also ineligible. No refutation of the earlier classical conjecture is asserted.
2. Jyothi–Ravi–Lakshmi, JCA27(1)(2026)119–127: candidate Problem1, monotonicity of nu*beta^(n+1)(nu)/beta^(n)(nu), is already addressed in this very paper. The neighboring problems and cited 2025 work were read as prior-theorem context, not selected as additional candidate questions. Actual definitions, Theorem1/proof, Theorem3/proof, Theorems4–5/proofs read. No novelty inferred from the word 'open' in the title. Only Problem1 was screened as a candidate; no neighboring question was pursued.
3. Selected: Bansal–Sokół, JMI13(4)(2019)911–918, final unnumbered conjecture p917. Literal h_r(z)=sum_(n>=1) (1+r²)/(n²+r²) z^n; conjecture says convex univalent for ALL complex r with Re r>0, and hence starlikeness of the normalized Mathieu series. Earlier paper develops real r>0. Source actual whole body, especially p917 and defining series, read. A real-parameter boundary-ODE mechanism was developed and completed below. However, real parameters alone do not prove the literal complex source claim. The complex failure is a routine coefficient/domain obstruction, expressly excluded by this campaign. Therefore no full substantive eligible nomination.

Closest-body comparison: Tomovski–Gerhold–Bansal–Soni, Axioms11(2022)568, actual publisher-version body from TUWien. Definitions, Lemmas1–3/proofs, Theorems1–3/proofs and conclusions were read. These use coefficient monotonicity/convexity on restricted real-parameter ranges, and do not establish the all-r convexity below in those read bodies. Alenazi–Mehrez, AIMS Mathematics8(12)(2023)30963–30980, actual publisher PDF: definitions1.4–1.5 and Lemmas1.1–1.3/proofs plus main theorem statements checked; its main object involves (n!)^beta, not n². Neither abstract constitutes clearance. 2019 precedes both followups. No exhaustive citation or specialist-database search claimed.

## Literal complex clause: routine, ineligible obstruction

Take r=1+2i, strictly inside Re r>0, with no denominator zero: Im(r²)=4. Then
 a2=(1+r²)/(4+r²)=(14+12i)/17,
 |a2|²=20/17>1.
For a normalized convex univalent h=z+a2 z²+..., p=1+zh''/h' has positive real part, p=1+2a2z+.... Applying Schwarz to (p-1)/(p+1) gives |a2|<=1, a contradiction. Likewise the normalized Mathieu series has second coefficient b2=2a2², |b2|=40/17>2; starlikeness would force |b2|<=2 by the same Schwarz argument applied to zS'/S. This is a complete elementary failure of both literal complex clauses, but is ONLY a routine coefficient/domain exclusion, not an eligible mathematical outcome. It says nothing negative about positive real r. No priority is claimed for this observation.

## Sustained real-parameter mathematics (uncounted restricted scope)

The following ordinary theorem is proved here: for every REAL r>0, h_r is convex univalent throughout |z|<1. It is not the full literal source claim and is not nominated. Dependencies: elementary Fourier/Poisson formulas, minimum principle, Schwarz lemma, and the classical analytic characterization of convex univalence. The last characterization is explicitly stated in the read 2023 primary body, p30964. No finite grid is used to establish a universal assertion.

Put g(z)=sum n z^n/(n²+r²), D=z d/dz. Then D h_r=(1+r²)g and convexity is equivalent to Re(Dg/g)>0 (quotient extended at0). First obtain all needed boundary/zero facts rather than assume this quotient is analytic.

On 0<t<2pi, let
 v(t)=(pi/2)*sinh(r(pi-t))/sinh(pi*r).
Its Fourier sine coefficient at n is n/(n²+r²): integrate sinh(r(pi-t))*sin(nt) on(0,pi), obtaining n*sinh(pi*r)/(n²+r²), and multiply by2/pi. Therefore Im g is the Poisson extension of the bounded odd boundary function v. On 0<t<pi, v(t)>0. Pairing positive/negative halves in the Poisson integral gives Im g(rho e^(i theta))>0 for 0<theta<pi, since P_rho(theta-t)>P_rho(theta+t) there. Reflection gives strict negativity in the lower half disk.

The same sine coefficients give the analytic representation
 g(z)=(2/pi)*integral_0^pi v(t)*z*sin(t)/(1-2z*cos(t)+z²) dt.
This follows by summing the absolutely convergent sine generating series for |z|<1. For real -1<z<1, the denominator is positive and the integral has the sign of z. Consequently g has no disk zeros except its simple zero at0.

For the subsequent boundary derivatives one can use
 g(z)=integral_0^1 cos(r log x)*z/(1-z*x) dx.
Coefficient integration gives integral_0^1 x^(n-1)cos(r log x) dx=n/(n²+r²). This integral extends analytically across each point of the unit circle other than1: on a sufficiently small complex neighborhood, the denominator is bounded away from0 uniformly in x in[0,1]. Dominated differentiation of every fixed order follows. Thus write its boundary values as u(t)+i v(t), with u,v smooth away from t=0 modulo2pi.

The coefficient identity (D²+r²)g=z/(1-z)² yields on the boundary
 u''-r²u=1/(4 sin²(t/2)),  v''=r²v.
Define W=u v'-v u'. Then on(0,pi),
 W'=-v/(4 sin²(t/2))<0.
At pi, the analytic integral representation above, or its limit from negative real z, gives
 u(pi)=-(1/pi)*integral_0^pi v(t)*tan(t/2) dt<0.
The endpoint integral is finite: v(t)=O(pi-t). Also v(pi)=0 and v'(pi)=-pi*r/(2sinh(pi*r))<0. Hence W(pi)>0, and W(t)>W(pi)>0 on(0,pi). Reflection gives W>0 on(pi,2pi). Because the boundary g has nonzero imaginary part except at pi, where u(pi)<0, it has no boundary zeros away from1. The relation d g(e^(it))/dt=i Dg(e^(it)) now implies
 Re(Dg/g)=W/|g|²>0 on the unit circle except1.

The singular boundary point1 must not be dropped from a minimum-principle proof. Here is its uniform control. Write
 g(z)=-log(1-z)+H(z),
 H(z)=-r²*sum z^n/[n(n²+r²)].
H and H' extend continuously to the closed disk by absolute convergence; H(1)=c is real and H(z)=c+O(|1-z|), uniformly inside the disk. Also Dg=1/(1-z)+O(1). Put w=1-z=rho e^(i phi). Inside the disk, |phi|<pi/2. With ell=log(1/rho),
 Re(Dg*conj(g))=((ell+c)cos(phi)+phi*sin(phi))/rho+O(ell+1).
For sufficiently small rho, ell+c>0. If |phi|>=pi/4, the second numerator term is at least pi/(4sqrt2), so the positive main term dominates the error uniformly. If |phi|<=pi/4, the first term is at least (ell+c)/sqrt2 and again dominates uniformly. Thus Re(Dg/g)>0 in a full punctured disk-neighborhood of1 intersected with |z|<1.

The quotient q=Dg/g extends analytically at0 with q(0)=1 and has no other poles in the disk. Apply the minimum principle for Re q on the disk with a small circular notch at1 removed. It is continuous on this compact closure and strictly positive on both its unit-circle boundary and its notch boundary by the preceding paragraphs. Positivity follows throughout. The removed neighborhood is already positive. Hence Re q>0 throughout the disk, and the analytic convexity criterion proves the stated real-parameter theorem. This closes the real theorem without a hidden zero-freeness or exceptional-boundary assumption.

The paper's real-parameter starlikeness consequence could be assembled using the classical convolution theorem cited there, but no separately verified original Ruscheweyh–Sheil-Small body is claimed here. This dependency and consequence are not proposed as another outcome.

## Other routes tested, and why they do not settle full scope

* Factor n²+r²=(n-ir)(n+ir): individual normalized factors are Bernardi-type kernels with imaginary parameters. A positive-real-parameter preservation theorem cannot be applied to these imaginary parameters without an additional theorem. No such bridge was assumed.
* Coefficient monotonicity: n/(n²+r²) initially increases whenever n(n+1)<r², since its consecutive difference has sign n(n+1)-r². Thus the decreasing-coefficient Fejér/Ozaki route from the read followup does not directly extend to all real r. This obstruction does not disprove convexity.
* The Laplace representation has cos(r log x) weights, which change sign for every positive r. It is not a positive mixture of convex kernels. The successful real proof uses the different sine-boundary positivity and Wronskian sign. None of those positivity steps extends to arbitrary complex r.

## Current registry and novelty limits

Before significant proof development, five live head endpoints were fetched at2026-10-29T15:01:19Z. All match r49 exactly: Omega dev e1d4e12fbc1f1f82e5f88362e931a52c778b4374; Omega main d7af67136d4478875778ac6e75eb5fbb8b3693a5; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; AIM8729eab98bafe409b66c5e39253bf56569a62327; Count dbf673741a54c7dc9d88a6aec0e8148a538f4a3a. Complete named cached scopes are reused with hashes in registry-screen.json: D5 12552, Problems1551; other scopes as recorded. Path lexical searches for Mathieu/Bansal/Sokol/Krasniqi/Nielsen reveal no relevant endpoint; an unrelated Sokolovs quantum filename is not a subject match. No full-dev absence or semantic completeness is claimed. Fresh public searches for exact paper title/conjecture and the multiplier located the read 2022/2023 followups, not a located exact real all-r proof. That absence is not novelty evidence or clearance. No worldwide priority or independent substantive review.

## Checks, strongest objection, disposition

check.py uses40-digit independent cos-integral quadrature at nine(r,theta) probes and compares the sine identity, v' and the boundary ODE. Errors<2e-40; W>0 at each. Fraction arithmetic checks the complex coefficients exactly. probe.py's initial interior double-precision grid is exploratory only (not proof, no all-parameter certification). The analytic proof above does not depend on either program. run.sh runs checks under capped_run.py: AS512MiB/CPU210s per process, wall230s and sampled groupRSS/CPU caps, BLAS1. Sampled caps can miss transients and reaped-child CPU; no enumeration or mathematical certificate is inferred from them.

Strongest falsifier/objection is decisive: the literal source quantifies complex r, while the substantive positive theorem here is real-only. The complex negative answer is routine. Therefore zero eligible nominations, no PROOF.md, no Lean/paper. If future work pursues the real theorem, root must first adjudicate whether it addresses a separately explicit source question and investigate classical multiplier/citation subsumption; neither is cleared here. Full literal positivity cannot be proved because of the exact complex witness. No access403/429 occurred; all actual fetches200, and no bypass was attempted.
