# A single presence jump: the exact two-time table

Author derivation, retaining the full frozen process target. This identifies the algebra needed for fixed coefficients; it does not yet prove the whole coefficient comparison.

## Exact local table

Suppose a common screened annulus reduces all relevant exterior observations to a single cap bit. Let u be the absent cap, v_b and v_w the caps after black/white insertion, with v_w<=u<=v_b. Put p=v_b-v_w and v=v_c for an independent fair color c. This notation includes p=0. For any payoff f on {0,1}², write

 f(u,v)=A+B u+C v+D uv.

For a birth, compare the joint before/after experiment with the no-particle experiment. Direct enumeration gives

 E_c[f(u,v)-f(u,u)]
 = (C+D/2) E_c(v-u) - D p/4.                         (1)

For a death, time ordering reverses the pair and the baseline is again absent at both sets of observation times:

 E_c[f(v,u)-f(u,u)]
 = (B+D/2) E_c(v-u) - D p/4.                         (2)

Indeed E_c(v-u)=p(1-2u)/2, and E_c[u(v-u)]=-p/4+E_c(v-u)/2. These are exact pointwise identities; they require neither a fair old cap nor conditional independence of old and new caps.

Now keep the inserted geometry present at all times, refresh its fair color once at the same time cut, and subtract its constant-fair-color history. Its local signed kernel is exactly

 p [f(0,1)+f(1,0)-f(0,0)-f(1,1)]/4 = -D p/4.        (3)

Thus geometric birth and death each equal ONE color-refresh signed kernel plus a signed FAIR-INSERTION marginal. The factor2 arises from the sum of birth and death intensities, not from replacing a jump by twice a refresh kernel. This matches the time scaling r_e/2.

## Actual source interface for the remainder

New actual readings: source A05-transfer.tex lines1-120 (seams, state fields, TV essential-supremum norm and transfer definition) and820-875 (fair-insertion corollary, first part of proof). Corollary tr:insertion states that, at unit intensity and a base-process screened seam of radius s, the signed difference of inside connection-state laws with and without an independent fair inserted nucleus has message norm <=C s^(-2-nu). The norm is the essential supremum over the output seam of total variation. It allows fixed exterior data not entering the screened inside. Rescaling gives C(e/h)^(2+nu) at physical radius h. This is precisely the marginal signed measure needed for the drift terms in (1)-(2), provided their coefficient is a bounded function of the exterior and seam, NOT of the unrevealed inside state.

The coefficient condition is important. It is satisfied when f is obtained by fixing exterior data and recording just the two possible outer cap states before/after the jump. One must not first condition on the inside event p=1 and then apply the fair-insertion bound: that conditioning need not preserve the even/isotropic signed message. Equations(1)-(2) deliberately keep p unconditioned and collect all marginal terms into the one signed measure.

The source theorem is accepted as stipulated; its earlier long transfer proof and the remainder of the corollary proof have NOT yet been read in full. No new primary claim follows from merely reading the corollary.

## Precise remaining assembly

For one separated site, exterior data can vary across observation times because of the other selected sites. A fixed common annulus still has the same base diagram at every time, so each time's exterior test reads the same cap bit; it produces one f(u,v) after grouping times before/after the selected jump. However the proof must implement this reduction without conditioning on inside pivotality, while controlling six-through-wall failures with the OTHER sites' arm factors. The scalar extra-arm estimate alone loses too many powers after normalization of a k-site coefficient. Independent buffered probes should retain those factors, but that mixed signed replacement estimate has not yet been written/proved here.

Once such a uniform fixed-k estimate is available, the one-replica forest majorant in generator-and-history-majorant.md permits summation. The lifetime density converges to one birth plus one death per unit time at the matched scale; short-lived histories were removed only for finite observation lists. Shared initial geometry in two replicas and full J1 tightness remain additional obligations. Equations(1)-(3) do not close them and do not by themselves determine a path law.
