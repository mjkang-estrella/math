# Ordinary counterexample candidate; source/eligibility HOLD, credit 0

29 October 2026. This is a complete ordinary construction for the class and determinant displayed below. The original and 2026 follow-up are available here only as indexed primary/author-upload mathematical passages; full direct files returned 403. Root must independently validate literal published source fidelity and prior-art/substantive eligibility before formal investment. This is not an acceptance, a Lean certificate, or a proof of a sharp universal upper bound.

## Literal target being refuted

Let D={z in C: |z|<1}, A the holomorphic functions on D with f(0)=0 and f'(0)=1, and phi(z)=1+z+z²/3−z³/9. The displayed symmetric-point class consists of f in A for which there is a holomorphic w:D→D with w(0)=0 and

    2 z f'(z)/(f(z)−f(−z)) = phi(w(z)).

At zero use the removable extension. For f(z)=z+sum(n≥2) a_n z^n, let

    H(f)=det [[1,a2,a3],[a2,a3,a4],[a3,a4,a5]]
        =2a2a3a4−a3³−a4²+a3a5−a2²a5.

The universal conjecture is |H(f)|≤1/16 for EVERY member of this class. This is Lupaş–Tayyah–Sokół, Symmetry17(2025)1244, Conjecture1; repeated as Conjecture1 in Tayyah–Hadi–Lupaş, Symmetry18(2026)1307. The latter states the upper bound769/12288 and continues to describe1/16 as conjectural. Its upper bound is NOT used as an input below.

## Construction on the whole disk

Put u=1/4 and

    w(z)=z²(u+z)/(1+u z),     p(z)=phi(w(z)),
    E(z)=(p(z)+p(−z))/2.

The denominator1+u z is nonzero on D. The exact identity

    |1+u z|²−|u+z|²=(1−u²)(1−|z|²)>0

shows |(u+z)/(1+u z)|<1 there; hence w is a Schwarz function, including w(0)=0.

E is even, analytic, and E(0)=1. Thus (E(z)−1)/z has a removable zero singularity and an analytic primitive G on the simply connected disk, uniquely normalized by G(0)=0. In fact G is even: this follows either by its Taylor series or from the oddness of its derivative. Define

    h(z)=z exp(G(z)),
    f(z)= integral from0 to z of p(t) exp(G(t)) dt.

The latter denotes the unique normalized analytic primitive; path independence holds throughout D. Both objects are holomorphic, h is odd, h'(z)=E(z)exp(G(z)), f'(z)=p(z)exp(G(z)), and f(0)=0,f'(0)=1. If F(z)=(f(z)−f(−z))/2, then

    F'(z)=(f'(z)+f'(−z))/2=E(z)exp(G(z))=h'(z), F(0)=h(0)=0.

Consequently F=h on D. For z≠0, h(z)≠0, and therefore

    2 z f'(z)/(f(z)−f(−z))= z p(z)exp(G(z))/h(z)=p(z)=phi(w(z)).

Both sides extend to1 at zero. This proves genuine full-disk source class membership, not merely compatibility of four arbitrary coefficient values.

## Optional strengthening: univalence

The displayed source definition only asks f∈A. Even if an independent source reading additionally requires univalence, the construction is close-to-convex. For |z|=1, write x=Re z. Then

    9 Re phi(z)=6+12x+6x²−4x³.

For x≥0 this equals6+12x+2x²+4x²(1−x)≥6. For x=−y,0≤y≤1 it equals6(1−y)²+4y³≥1/2: use y≤1/2 and y≥1/2 separately. The harmonic minimum principle gives Re phi≥1/18 on the closed disk. Thus Re p>0 and Re E>0 on D. Since z h'/h=E, the standard analytic starlikeness criterion makes h starlike; Re(z f'/h)=Re p>0 then makes f close-to-convex and univalent by the classical close-to-convex criterion. This optional strengthening uses named classical analytic criteria; it is not needed to refute the displayed A-based class claim. A formal endpoint requiring univalence must prove/import those criteria, not leave them as premises.

## Exact determinant, independently reconstructed

More generally keep0<u<1. Expansion gives

    w(z)=u z²+(1−u²)z³−u(1−u²)z⁴+O(z⁵),
    p(z)=1+u z²+(1−u²)z³+[−u(1−u²)+u²/3]z⁴+O(z⁵).

Compare coefficients in z f'=p h, using h=(f−f∘neg)/2. This gives

    a2=0, a3=u/2, a4=(1−u²)/4,
    a5=[−u(1−u²)+5u²/6]/4.

Therefore

    16 H(f)=u⁴−u³/3−1.

In particular at u=1/4,

    a2=0, a3=1/8, a4=15/64, a5=−35/768,
    H(f)=−769/12288,
    |H(f)|−1/16=1/12288>0.

This refutes the ENTIRE universal1/16 claim. It is an interior-disk holomorphic witness with a strict rational margin, not a typo, domain, equality-case or endpoint correction. Indeed every0<u<1/3 in this construction violates the conjecture. No numerical evidence, finite enumeration, generic coefficient-realizability assumption, or 2026 upper-bound theorem is needed.

## Adversarial checks and limits

The determinant uses +a3a5, as required by the literal3×3 matrix; a malformed minus sign in an indexed line of the original paper is not used. The stated conjecture is about the determinant, and the2026 definition/formula confirms this. The map w is a genuine finite Blaschke product on D even though it has unit-modulus boundary values. Neither the class nor its subordination requires a strict boundary bound. The f−f∘neg denominator is nonzero off zero by the constructed exponential, rather than assumed.

Strongest substantive objection: this witness comes from setting the first Schwarz coefficient to zero and a remaining Schur parameter on its unit circle. Its modulus exactly attains the already-published2026 upper bound. It could be considered a routine missed equality case of that paper; root must judge. A full prior proof/refutation or a later corrected published version has not been ruled out. Direct source files and the2026 full argument/conclusion remain403HOLD. No worldwide priority is claimed.
