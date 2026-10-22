# Structural r189 — prefreeze construction record

Disposition: PREFREEZE / no nominee. These are research derivations, not a frozen author theorem, correctness review, contribution grade, or acceptance claim. Source313 and every operative upstream proof at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The construction below was developed after the complete source text, the selected original-history passages, and the primary proof passages recorded in private/READING-LIMITS.md were read. No old full target is revised.

## 1. The operation being investigated

The one direction developed here is certified finite-jet reconstruction of the continuous cohomology used by Source313. For every prime p, height n >= 1, integral periodicity weight w, and finite cohomological window 0 <= i <= d, take the manuscript's ordinary stabilizer P_n over its finite Honda field k and its coefficient M = L_1^w over A_1 = k[[u_1,...,u_(n-1)]]. At the n = 1 endpoint A_1 = k. The finite extended Galois action is retained when passing to G_n; it is not replaced by averaging. The desired operation would produce exact finite k-linear cohomology data from finite jets, with a certified termination bound, at every one of these parameters. Source auxiliary whole division/marking coefficients are used in an attempted proof of that operation, not added as arbitrary semilinear coefficients.

More precisely, for a compact finite-free group-ring resolution P and C = Hom_cont,k[[P_n]](P,M), let F^N C = (m_A^N M)^(r_i) in degree i. One wants a finite N_0 and an effectively specified L(N) >= N such that, in the given window,

    I_N^i := im[H^i(C/F^L(N)) -> H^i(C/F^N)]

is the image of H^i(C), and I_N^i is isomorphic to H^i(C) for N >= N_0. The same output must distinguish genuine classes from classes that disappear at some later jet; a finite plateau is insufficient. This is an unfrozen research objective. No algorithm with those guarantees is established here. In particular, existence of an abstract finite-free resolution is not an assertion of an effective construction of its entries. Below, first grant finite-jet access to such a resolution in order to expose the deeper remaining obstruction even under this favorable assumption.

This direction asks for a new effective operation on the actual source coefficients. It does not ask for the already paid finite generation of the sphere, an all-degree uniform torsion exponent, a dualizable-spectrum extension, or an identification of all homotopy groups from E_2 alone.

## 2. An exact finite-matrix system

Write r = n-1 and rho = rank_A(M), equal to one for the selected periodicity line. Source Section 2 gives a resolution P_i = k[[P_n]]^(a_i), finite free in each degree; there need not be a finite length resolution when the group has p-torsion. Consequently C^i = M^(a_i) is a compact k-vector space. The action preserves m_A^N M: a local semilinear automorphism preserves m_A, and the line character is a unit. The completed group-ring matrices defining the differential therefore preserve F^N, by continuity. This gives actual finite complexes

    C_N^i = C^i/F^N C^i,
    dim_k C_N^i = rho a_i binomial(N+r-1,r)      (r > 0, N >= 1).

For r = 0 the dimension is rho a_i and the filtration is already zero for N >= 1. For the extended stabilizer, use the same construction over F_p and a finite-free F_p[[G_n]] resolution, retaining its semilinear Galois action; coefficient dimensions acquire the factor [k:F_p]. This avoids an averaging argument even when p divides the Galois degree. Finite coefficients alone do not permit replacement of P_n by a finite quotient for cohomology; we keep the full resolution. Its action on each individual coefficient quotient factors through a finite quotient, which is enough to evaluate the matrix entries if their jets are available. Conflating these two assertions would lose higher continuous cohomology.

For a finite window H^0,...,H^d, differentials through C^(d+1) are used. A quotient of the complex truncated too early would add false top-degree classes. In each finite complex compute Z_N^i = ker d_N^i, B_N^i = im d_N^(i-1), and a basis of Z_N^i/B_N^i by finite field elimination. Transition matrices come from projection of cycle representatives followed by reduction modulo B_N^i. These are unambiguous induced maps even though the representatives and bases are not canonical.

The transition maps C_(N+1)^i -> C_N^i are surjective. Thus C = lim C_N is also the derived inverse limit of these complexes. The usual product-cone proof of derived inverse limit gives

    0 -> lim^1 H^(i-1)(C_N) -> H^i(C) -> lim H^i(C_N) -> 0.

Every H^i(C_N) is finite. Images into a fixed finite vector space stabilize, so the tower is Mittag–Leffler and lim^1 is zero. Therefore

    H^i(P_n,M) = lim_N H^i(C_N).                         (2.1)

This equality concerns the chosen compact topology and actual continuous group action. No exchange of a perfected Laurent direct limit with an adic inverse limit is involved.

## 3. Persistent images and finite detection, with proof

Set V_N = H^i(C_N), and J_N = intersection over L >= N of im(V_L -> V_N). Because V_N is finite, J_N equals one of these finite-stage images, though the argument does not locate that stage. The image of lim V_L -> V_N is J_N. To prove the nontrivial inclusion, fix v in J_N. For every L the finite set of partial compatible sequences ending at L and projecting to v is nonempty. These finite sets, or equivalently their compact cylinder sets in the product of the V_L, have the finite intersection property. Their intersection is a compatible infinite sequence. This proves the assertion without assuming all original transition maps are surjective. It also proves J_(N+1) -> J_N is surjective.

Source Theorem thm:coeff-finite now makes H = lim V_N finite. Let K_N = ker(H -> V_N). The descending family K_N has intersection zero, since an element of an inverse limit is determined by all coordinates. Finiteness of H gives an N_0 with K_N = 0 for all N >= N_0. Hence

    J_N is canonically isomorphic to H for N >= N_0.     (3.1)

For each fixed N choose L(N) where the image has reached J_N. These choices can be made monotone by increasing them. Thus the desired inverse system is non-effectively pro-isomorphic to the constant finite space H. This is a proved reduction from the paid source, not a nonroutine nominee. It is stronger than merely saying that a limit is finite: it supplies a finite detector and finite persistent-image descriptions at every jet, but without computable witnesses.

For finite diagrams of coefficient maps preserving the filtrations, the J_N construction is natural. A single sufficiently large detector works for finitely many objects and finitely many degrees by taking their maximum, and a single L(N) works by taking the maximum of their stabilization stages. Thus source finite diagrams do not create an additional *existential* naturality obstruction at this point. This observation does not make these maxima effective.

## 4. A continuous contraction and an explicit primitive modulus interface

There is another stronger, chain-level reduction. Images of continuous maps between compact Hausdorff k-vector spaces are closed. For the complex C, put Z^i = ker d^i and B^i = im d^(i-1). Exact sequences of compact k-vector spaces split continuously: continuous duality changes them into exact sequences of discrete k-vector spaces, which split by ordinary basis choices. Applying this twice gives

    C^i = B^i direct-sum Htilde^i direct-sum L^i,
    Z^i = B^i direct-sum Htilde^i,
    d: L^i -> B^(i+1) a continuous isomorphism.

Htilde^i is a finite space representing H^i(C), by Source313. Define j by these representatives, p by projection, and h on B^i by the inverse of d:L^(i-1)->B^i, zero on the other summands. Then

    pj = 1,   dj = 0,   pd = 0,
    dh + hd = 1-jp,   h^2 = 0,   hj = ph = 0.           (4.1)

The splittings are k-linear. They are not A-linear, canonical, multiplicative, or claimed to commute strictly with all auxiliary actions. In particular no multiplicative finite model has been constructed.

Continuity of p and h gives two finite-jet facts. For each relevant i, p vanishes on F^(N_0) C^i for some N_0. For every N there is b_i(N) such that

    h(F^b_i(N) C^i) is contained in F^N C^(i-1).         (4.2)

For any boundary z in F^b_i(N) C^i, one has dz=0 and pz=0, so (4.1) yields z=d h(z) with a primitive in F^N. Equation (4.2) is precisely a uniform primitive-lifting modulus. Its existence follows from compact splittings. No numerical modulus is supplied by that proof.

These maps also quantify the persistent-image calculation *once their continuity moduli are known*. Choose N sufficiently large that p(F^N C^i)=0. For L >= N with h(F^L C^(i+1)) subset F^N C^i, let z in C^i represent a cycle modulo F^L. Since dz is in F^L, (4.1) gives

    z - j p(z) = d h(z) + h(dz),

whose last term vanishes modulo F^N. Thus the image of [z] at level N is the class of j p(z), hence comes from genuine cohomology. Conversely genuine cocycles lift at every L. It follows that this L realizes J_N. Injection follows as well: if j(v)=dy+e with e in F^N, then applying p gives v=0. This gives the specific algorithmic interface, not just a name for an unspecified gap: compute and certify the finite factorization level of p and the degree-(i+1) primitive modulus for h.

## 5. A convergent correction certificate

An approximate finite model could certify these maps without guessing that a plateau is final. The following calculation identifies a sufficient exact interface. Let H be a finite graded k-vector space with zero differential. Suppose continuous maps j,p,h satisfy dj=0, pd=0, pj=1, hj=ph=0. Put

    E = 1-jp,   T = E-(dh+hd).

Then T commutes with d, Tj=0 and pT=0. Suppose one additionally proves, in every degree needed for the window,

    T(F^N C) subset F^(N+1) C for every N >= 0.         (5.1)

This is an all-orders estimate, not a test up to a chosen finite order. The series R=sum_(a>=0) T^a converges continuously for the complete filtration: T^a(C) subset F^a C. Define h'=hR. Since T commutes with d,

    dh' + h'd = (E-T)R = E.

Indeed E T^a = T^a for a>=1, so the partial sums telescope to E-T^(A+1), whose last term tends to zero. Thus j,p,h' give an actual contraction and H is the exact cohomology in the stated degrees. The continuity modulus of h', when obtained from represented maps and filtration estimates, supplies the bounds of Section 4.

This is a usable verification criterion but not a source-specific construction. A candidate finite certificate must provide exact represented j,p,h (or a proven correction scheme making them exact), proofs of the chain identities, and the global estimate (5.1). Checking finitely many coefficients of those identities does not suffice. Producing those represented operators for the manuscript's stabilizer differential is the unpaid operation. We do not declare the criterion itself to be a substantial new theorem.

## 6. Feeding the actual normalized-transfer operation into this interface

Source Section 7 constructs a *single normalized* inverse-Frobenius Cartier operator S using the invariant volume form, and natural root comparisons for each finite auxiliary diagram. If h_0 is its one-step root factor, its lattice bound is

    S(x^(-D) A') subset x^(-ceil(D/h_0)-c) A'.          (6.1)

Let D_* be an integer strictly larger than (c+1)/(1-h_0^(-1)). Since ceil(D/h_0) <= D/h_0+1, iteration gives the explicit estimate

    D_a <= D/h_0^a + (c+1)(1-h_0^(-a))/(1-h_0^(-1)).   (6.2)

Consequently an initial pole bound D is absorbed by the fixed lattice x^(-D_*)A' after any a with

    D/h_0^a <= D_* - (c+1)/(1-h_0^(-1)).              (6.3)

The right side is positive. This converts the manuscript's eventual pole absorption into a numerical bound *relative to its chosen c,D_*,h_0*. It neither computes those source constants uniformly nor bounds cohomology dimensions.

The source also retains one finite Yoneda boundary operator B after choosing the finite equivariant diagram and shrinking U once. In fixed integral frames its pole loss is bounded by a constant C_B. If a normalized positive representative w has x-order at least epsilon>0, its h-th power has order at least h epsilon, and the represented B(w^h) has order at least h epsilon-C_B. Any fixed finite-frame loss can be included in C_B. Thus B(w^h) is in x^(-D_*)A' whenever

    h epsilon >= C_B-D_*.                            (6.4)

With h=h_0^a this is an explicit logarithmic threshold once the diagram, its root normalization, epsilon and C_B are fixed, and once the source's high-transfer comparison has begun. The scalar c_q in the source is a nonzero constant and does not alter this valuation bound. This calculation uses the *one* operator and *one* U from Section 10, not different shrinks depending on h. At height one the source instead uses the toral split S Fr^nu=1; it is not substituted silently for higher-height distribution theory.

Equations (6.2)-(6.4) genuinely integrate the strongest source operation. What they bound is pole absorption in the marked, x-localized finite diagram. The target filtration is the full deformation-adic filtration of the original compact cochain complex. These are distinct directions. Even for one variable the usual Cartier operator

    C(x^(h a+h-1)) = x^a,
    C(x^b) = 0 when b is not congruent to h-1 mod h

sends arbitrarily high positive orders to orders divided approximately by h. It is continuous, but it is not a tail-improving operator of the form (5.1). Its adjoint absolute Frobenius expands positive order on the residue/Laurent side. Section 9's positive-part acyclicity uses this adjoint expansion *after* Baire/Pettis gives openness of boundaries in a complete weighted cycle step. It cannot be read as an explicitly bounded contraction of original deformation jets.

In more variables x-pole control also says nothing by itself about every other deformation coordinate. The comparison would have to transfer the weighted complete-step primitive bounds back to F^N C, including basis changes, all finite marking/Amitsur descent maps, and the selected finite resolution. No such comparison modulus was obtained here.

## 7. The strongest coherent Cartier stabilization does not fill that interface

Blickle–Boeckle Proposition 2.14 gives actual stabilization of C^a(M) for a coherent Cartier module. The proof uses Noetherian support descent and then finite length after placing a fixed ideal multiple of M in every image. Proposition 4.1 and Theorem 4.6 strengthen this to finite length of Cartier crystals up to nilpotence. These are stronger than a mere compactness slogan and were read as proofs, including their support-ideal and F-finiteness mechanisms.

They apply to a coherent module over the structure ring, with a compatible inverse-Frobenius map. Group cohomology here is not naturally a coherent A-module. Already on degree-zero group cochains,

    d(a m)(g) = a d(m)(g) + (g(a)-a) g(m).            (7.1)

Thus the group differential is not A-linear, and neither cycles nor boundaries carry the required A-submodule structure in general. The same defect remains in a compact resolution, since its entries act semilinearly. Having a Cartier operation on the coefficient lattice does not erase (7.1). Stabilizing coefficient-module images therefore does not stabilize the jet images of group cohomology by the coherent-module theorem. Source Section 9 correctly works instead with compact k[[z]]-modules (z acts by S), finite inverse-limit images, and locally S-nilpotent localization kernels. Those are paid operations; their topology is not the deformation-adic topology required for (4.2).

The remaining possibility is to construct a compatible filtered homotopy directly, using the finite Yoneda diagrams plus their residue adjoints. Sections 4-6 give the exact identities and bounds that such a construction must produce. We carried that route as far as the explicit absorption inequalities and chain correction. The global primitive modulus after descent is still not constructed, even with finite-jet access to the stabilizer resolution granted.

## 8. Why finite testing cannot certify the missing estimate

This is a control calculation, not a counterexample to any source statement. Let R=k[[x]] and take the compact two-term complex

    D_L = [ R --x^L--> R ] in degrees 0 and 1,

where L>=1. It has H^0=0 and H^1=R/(x^L), both finite. For N<=L the truncated differential is zero, so H^0(D_L/x^N)=H^1(D_L/x^N)=k^N. At an arbitrary level N their dimensions both equal min(N,L). For K>=N, the image rank on H^0 is

    max(0, N-max(K-L,0)),

whereas the image rank on H^1 is min(N,L). Thus the stable H^0 image is zero and the stable H^1 image has dimension min(N,L); H^1 is detected at N>=L. A correct primitive modulus is b(N)=N+L.

For L and L' both beyond every inspected jet, the inspected finite complexes are identical, both full complexes have finite cohomology, but the final H^1 dimensions are L and L'. Long finite plateaus are compatible with two different finite answers. This disproves the proposed inference 'finiteness plus observed stabilization gives a certified cutoff' for general compact complexes, not for the particular source family. Source-specific extra structure might still supply the required cutoff. The bounded calculation in private/finite-matrix-control.json checks this formula at small integer parameters; it is an arithmetic control, not a mathematical gate.

## 9. Descent, completion and finite spectra: no hidden shortcut

Devinatz–Hopkins Lemma 5.11 proves that a universal horizontal line for an Adams tower gives actual null composites in that tower, by testing against every spectrum Z. Lemma 5.12 then controls localization and homotopy inverse limits. Heard Theorem 4.13 supplies the relevant finite-page horizontal line independently of the spectrum. Source Section 12 uses this to keep only finitely many descent filtration pieces in each homotopy degree. These strong facts are paid and apply to the Adams/totalization filtration. They do not identify that filtration with F^N of the deformation coefficients; substituting one for the other would assume precisely an additional comparison.

Once mod-p homotopy groups are finite, the actual p-power cofiber sequences make pi_j(X/p^a) finite for each a. Their finite towers have vanishing lim^1, and derived p-completeness gives pi_j(X)=lim_a pi_j(X/p^a). Compact Nakayama gives finite generation over Z_p. This uses the genuine Moore cofiber, not the false assertion that every pi_j(X/p) is killed by p. Neither compact Nakayama nor the finite p-power tower computes a torsion exponent, a generator count, spectral-sequence differentials, or hidden additive extensions.

Thus even a successful finite E_2 calculation would not itself compute the sphere's integral homotopy groups: differential and extension data would be additional tasks. They are not asserted as part of this round. Finite p-local spectra follow by the source's finite cofiber/retract argument, with finiteness and p-locality retained. Li's height-two invertible examples and Hovey–Strickland's interpolated-degree calculations prevent treating all dualizable objects as if they were finite p-local inputs.

## 10. Exact endpoint

The completed reduction is: finite source cohomology -> finite inverse-limit matrix system -> eventual canonical persistent images -> a non-effective continuous contraction -> an explicit convergent-correction certificate and primitive-modulus interface. The actual normalized transfers supply explicit relative pole-absorption thresholds and fixed-diagram compatibility, but not the required deformation-adic primitive modulus after residue/marking descent. Coherent Cartier stabilization does not apply to the semilinear group-cohomology complex, and the Adams horizontal line controls a different tower.

The unpaid operation is to construct source-specific represented chain maps and a certified all-orders tail contraction (or equivalently sufficiently effective projection and primitive moduli) compatible with the actual stabilizer action and marking descent, for all p,n,w and every finite degree window. A complete implementation would also need effective finite-jet access to a certified compact resolution; this note deliberately grants that interface to isolate the stronger obstruction. No universal algorithm, rank bound, impossibility theorem, or new full theorem is claimed. No theorem was frozen and no author-proof nominee was developed.
