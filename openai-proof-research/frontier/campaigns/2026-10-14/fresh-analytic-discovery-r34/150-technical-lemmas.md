# Collision-clock lemmas and a negative control

Myeongjin Kang; no affiliation. CC BY 4.0. These deductions are technical support, not the full target or a nomination. Pinned source truth is stipulated. They have not received independent review.

Let Q be any fixed nondegenerate triangle with an irrational angle. Let B be its regular collision section, T its collision map, nu=cos(phi) ds dphi/(2P), and tau its positive flight roof. Here P is the perimeter. Vertex and grazing trajectories are removed only as null sets, not by a uniform clearance restriction. Flight coordinates give the physical-time Liouville measure proportional to dnu dt on 0<t<tau. The roof is positive almost everywhere and bounded by diam(Q).

## 1. The oriented double flow is weakly mixing

This is a short extension of the actual source conclusion, using its transverse-rigidity proposition on the double unchanged. Let f be a bounded geodesic-flow eigenfunction of frequency lambda on the double. The proposition gives grad f=i lambda v f in oriented flat charts. On each triangle sheet, fold its coordinates and tangent vector to Q. In these coordinates f has the form c_1(v) exp(i lambda x.v) on sheet1 and c_2(v) exp(i lambda x.v) on sheet2. The spatial equation has this form also in the oppositely oriented sheet: both the gradient and vector transform by the same orthogonal reflection, and Yf=0 is orientation independent.

Put an irrational-angle vertex at the origin. If R_i x+d_i reflects in side i, the connected crossing chart gives

c_1(v)=c_2(R_i v) exp(-i lambda d_i.v)  (almost every v).

For the two sides through the origin d_1=d_2=0. Thus c_2 is invariant under R_2 R_1, an irrational circle rotation. Its circle Fourier coefficients show that c_2 is constant almost everywhere; then c_1 is the same constant. On the third side d_3 is nonzero, so a nonzero amplitude would require exp(-i lambda d_3.v)=1 almost everywhere. Continuity and the interval of values of d_3.v force lambda=0. Thus f is constant. For an arbitrary L2 eigenfunction, f/(1+|f|) is a bounded eigenfunction with the same frequency; injectivity recovers constancy. The source compact-operator spectral lemma then proves weak mixing of the double flow.

No new energy estimate was used. This is not offered as substantial.

## 2. The physical collision map has no eigenvalue -1

Source flow ergodicity gives ergodicity of T: an invariant section set and its complement, if both of positive nu measure, suspend to two positive-measure invariant flow sets because tau>0 almost everywhere.

Suppose h(Tz)=-h(z), h in L2(nu), h nonzero. Replace h by h/(1+|h|) to make it bounded without changing the equation or nonvanishing. For a regular interior state use its last collision z and set F=h(z), constant on that flight. On the oriented double set f=+F on sheet1 and f=-F on sheet2. Each forward collision changes the last-collision value by -1 and also changes sheet, so f is invariant for the double geodesic flow. This equality is an L2 equality for each fixed time; finite collision itineraries and the removed null set justify the definition. Part1, or its lambda=0 argument alone, makes f constant. The deck involution reverses the sheet sign while fixing folded position and velocity, hence sends f to -f. Its measure preservation forces the constant to be zero, a contradiction.

To conclude T² is ergodic, let Ug=g compose T be its unitary operator and suppose U²g=g. Then g_+=(g+Ug)/2 is U-invariant and g_-=(g-Ug)/2 satisfies Ug_-=-g_-. The first is constant by ergodicity, the second is zero by the previous paragraph. Thus every U²-invariant L2 function is constant.

This establishes T²-ergodicity only. Powers of order three, arbitrary roots of unity and irrational eigenphases are not eliminated.

## 3. A negative control in the same stipulated geometry

Take as section of the double flow the open seams, recording the sheet entered after a collision. Its map is

T_hat(z,sigma)=(Tz,-sigma), sigma in {+1,-1}.

Its normalized section measure is nu times the fair sheet law, and its roof is tau(z). Part1 proves that its suspension is weakly mixing. Nevertheless sigma is a nonconstant eigenfunction of T_hat with eigenvalue -1. Thus this actual geometric section directly falsifies the proposed general implication “a weakly mixing suspension has a weakly mixing first-return map.” It does not refute weak mixing of the physical one-sheet map T.

## 4. Exact seam and Fourier calculation

For an eigenphase omega=exp(i alpha), define F to be the last-collision value h(z) on both sheets without a deck sign. In a crossing chart with normal coordinate x_n, f_+(v)=omega f_-(v) if v_n>0. If v_n<0, a forward trajectory crosses in the other direction, so f_-(v)=omega f_+(v). Consequently the geometric transition from minus to plus is multiplication by

J_alpha(theta)=exp(i alpha sign(cos theta)).

Changing the selected normal conjugates the multiplier and has no effect on the norm calculations. With normalized circle measure its coefficients are

j_0=cos alpha;
j_m=(2i sin alpha/pi) sin(m pi/2)/m, m nonzero.

This follows by splitting the circle into cos theta>0 and cos theta<0, integrating exp(-im theta), and using sign(cos theta)=2 1_{(-pi/2,pi/2)}-1. The formula works also for negative m.

For P_+ the projection to nonnegative angular frequencies, restrict [P_+,J_alpha] to input modes k=-N,...,-1 and output modes j=0,...,N. Its entry is j_{j-k}. The number of pairs with j-k=m is c_N(m)=m for 1<=m<=N and c_N(m)=2N+1-m for N<m<=2N. Therefore the squared Hilbert--Schmidt norm is exactly

H_N(alpha)=(4 sin²alpha/pi²) sum_{m=1}^{2N} c_N(m) sin²(m pi/2)/m².

For m<=N the odd terms sum to (1/2)log N+O(1). The remaining sum is bounded by sum_{N<m<=2N} N/m²=O(1). Hence

H_N(alpha)=(2 sin²alpha/pi²) log N+O_alpha(1).

For sin alpha nonzero the full Hankel block is not Hilbert--Schmidt. The commutator operator itself remains bounded: ||[P_+,J_alpha]||<=2||J_alpha||=2. No failure of boundedness, no forced spectral atom, and no impossibility of a more refined seam estimate follows from this calculation. At alpha=0 or pi every off-diagonal coefficient is exactly zero; the parity argument is consistent with this control.

## 5. Why the source cutoff argument does not transplant

The source localized coefficient estimate bounds one coefficient energy by the product ||Aw||_2 ||1_E grad w||_2 (plus its spectral correction). Its vertex region has base area O(eps²), and each derivative is bounded by C H/eps. Both norms are O(H), uniformly in eps. Cutting out an entire fixed-length seam instead has area O(eps), giving the crude bounds O(H eps^(-1/2)) for each norm and O(H²/eps) for their product. A stronger estimate might exploit traces or cancellation, but the source estimates alone do not do so.

The problem cannot be removed by declaring the two sheets to be a flat scalar bundle with constant transition omega: consistency of reversing a geometric crossing would then force omega=omega^{-1}. For general phases the two half-circles carry opposite exponents, as computed above. A higher collision-count cover is therefore not automatically the unit tangent bundle of a finite flat-surface cover.

The remaining full-scope obligation is an estimate or classification for bounded flight-constant fields with these three direction-dependent unitary seam transmissions. It must prove that no nontrivial omega survives for every triangle in the stated class, while controlling arbitrary measurable h and grazing directions. Finite-mode truncation, positive clearance, a special spectral phase, or generic angle restrictions would change the target.
