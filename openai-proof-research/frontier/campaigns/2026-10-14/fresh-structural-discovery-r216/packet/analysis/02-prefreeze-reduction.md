# Prefreeze feasibility record

This record precedes the frozen statement and author-proof file. No mathematical verdict. The following calculations were developed in the conversation after the complete source read and after actual AIS §§3.1–3.2,3.4–3.7,4.1–4.2; CP §§2.2–2.3,3,5; Kragh §6; AACK §4.1; and ACGK v3 §3 were read. Some of these interfaces cite intermediates not read independently; exact limits are retained in the private reading log.

## Common-endpoint difference calculation

If F_i on Q×R^{r_i} generate the same connected embedded exact L, with generating maps diffeomorphisms, then D(q,u,v)=F_0(q,u)-F_1(q,v) has full critical locus identified with L. Its equations are F_{0,u}=F_{1,v}=0 and F_{0,q}=F_{1,q}; injectivity of the generating parametrizations gives the diagonal over the common image. The two induced primitives differ by a constant, so D is constant there. A Hessian-kernel vector satisfies both linearized critical equations and equality of the two linearized momenta, hence comes from one tangent vector of L under the two parametrizations. Thus the Hessian kernel is exactly tangent to this critical manifold: D is Morse–Bott.

This is the actual input to CP's difference-function argument, not a family with one critical point in each Q-fiber. For source F and fixed b, the partial difference in (v,w,z) only gives w−z=t v, not t=0; the b-momentum test which separates source branches has been omitted. Thus one cannot silently keep b as a parameter while using the full diagonal conclusion. CP's full construction stabilizes negative eigenbundles, builds exit-domain complements, straightens high-codimension cores, and reduces to product cobordisms. Its product operation has Euler factor χ(P,∂P); in particular odd-sphere multiplication can vanish. None of this establishes a pairwise invariant of the selected tube classes. Also g⊕(−g) is not asserted to be the group-theoretic inverse cancellation: ACGK Lemma 3.18 proves that cancellation for quadratic forms, not arbitrary tubes.

## Explicit doubling for the source's stronger uniform infinity condition

Let F be a smooth Morse family on compact Q, exactly equal to smooth-off-zero homogeneous g outside a fixed w-ball, with |∇_w g|≥c|w|, and generating a closed embedded exact L. Choose an odd birth function D(t), equal to t^3−t for |t|≤1, equal to t for |t|≥2 after an appropriate wider transition if needed, and with D'(t)>0 for |t|>1. The actual choice must be made compatible with those endpoint values (a wider transition can be used); only its two critical points and their nonzero opposite values matter. Positive dilation D_s(t)=κD(t/κ) changes their values to ±s. Set E_s=D_s−t. With α_A(w) a radial cutoff equal to 1 on |w|≤A and 0 on |w|≥2A, consider

H_s(q,t,w)=F(q,w)+t+α_A(w)E_s(t).

For s in a fixed compact interval, |E_s|≤M. On the annulus A≤|w|≤2A the w-gradient has lower bound cA−Cα M/A. Taking A beyond the original critical ball and cA²>Cα M removes every extra critical point. Thus the full vertical critical set is precisely Crit(F)×Crit(D_s). It generates the two primitive shifts of L. Embeddedness makes these a genuine chord-free Legendrian two-copy isotopy. This is a direct lift of the doubling construction, with one uniform A, not merely fiberwise existence.

For a large endpoint s, deform F to a smooth extension G of g. Along F_u=(1−u)F+uG every critical point lies in a uniform ball. Choose s exceeding the absolute values of all these possible critical values. H_{s,u}=0 is then fiberwise regular even when F_u ceases to be Morse. Thus the natural partition-tube class is reduced to an operation on g alone. Replacing G near zero by the C^1 homogeneous g changes no regular zero-level class, by a sufficiently small C^1 deformation and smooth approximation.

## The nontrivial comparison calculation

After positive dilation of (w,t), use D(t)=t^3−t near all of its critical points. In the homogeneous case any positive double separation can be used, since g has only critical point 0 of value 0. Let α(r) be nonincreasing, equal 1 near r=0 and 0 for r≥2A. Choose a(r) nondecreasing, zero near zero, equal r² for large r, and ≥2 wherever α=0. Interpolate

B_u(r)=(1−u)α(r)+u,
C_u(r)=1−2B_u(r)+u a(r),
H_u(w,t)=g(w)+B_u(r)D(t)+(1−B_u(r)+u a(r))t.

Outside the region where D=t^3−t, the t derivative is positive, because D'>0 and the second coefficient is nonnegative. At a possible zero-level critical point inside that region,
3B_u t²+C_u=0 and Euler's identity for g gives
r C_u'−r B_u' C_u/(3B_u)−4C_u/3=0 when t≠0.
But B_u'≤0, C_u'≥−2B_u', C_u/B_u≥−2, and C_u<0, making the left side strictly positive. If t=0, the w equation is ∇g=0, so w=0, where C_u=−1. Thus there is no zero-level critical point. The possible B_u=0 region has positive t derivative directly.

At u=1 the function is g+D(t)+a(r)t. Change D to t³−t through functions whose derivative stays positive outside |t|≤1, then change a(r) to r² through nondecreasing nonnegative functions. The same Euler calculation gives regularity. Outside a fixed w-ball all these zero sets are graphs with strictly positive t derivative; translating by the unique graph height and using a radial cutoff makes the entire isotopy a compactly supported family of partitions. This step needs a full properness/uniformity proof in the author proof.

Finally, stereographic projection from the fixed pole a=1,b=0,w=0 of S^{N+1} in R^N_w⊕R_a⊕R_b gives
w_sphere=2w/(1+ρ²), b_sphere=2t/(1+ρ²), a_sphere=(ρ²−1)/(1+ρ²), ρ²=|w|²+t².
The sign of g(w_sphere)+2a_sphere b_sphere is the sign of
 g(w)+t(ρ²−1).
Thus this endpoint is the original tube stabilized by one positive and one negative square. Angular smoothing near the pole gives the usual standard-halfspace chart; the comparison with graph straightening must be included, not assumed.

This suggests the chosen generating-family class, modulo rigid tubes, equals the natural coset for source realizations. Unlike merely applying transport, this supplies the missing comparison of the arbitrary infinity data with the canonical doubling output. Its entire proof, including infinity normalization, is still to be written and checked against the frozen scope.

## Finite family algebra

Let x generate the Z/8 summand of the source's A_(2). The preceding boundary image is killed by 2, so x maps to a∈ker gamma_* of order 4 or 8. Hence 0,a,2a,3a are distinct. Represent the last three at one common finite diagonal stage and apply the source embedded realization with common choices of constants. If the natural-coset comparison above closes, an isotopy of L_j and L_k implies that (j−k)a is rigid after restriction to S^9×{v0}. Applying gamma and injectivity of BJ on pi_9 BO forces that rigid class to vanish, a contradiction. This compares every pair, rather than only each nonzero member with zero.

The target below is an existence theorem for one sufficiently large even N. No explicit stage bound or all-N statement is contemplated. The parent alone determines correctness, contribution, acceptance, and count; no new-to-literature claim is established by the guarded history scan or by the listed primary reads.
