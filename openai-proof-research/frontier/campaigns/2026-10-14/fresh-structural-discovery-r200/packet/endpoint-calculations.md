# R200 endpoint calculation — a concrete failure of the naive Schur upgrade

This is an auxiliary prefreeze derivation. It preserves the full Source324 constructions as stipulated true and changes only the norm proposed in this round. It does not challenge the upstream no-c0 theorem. It does not rule out other Schur absorption constructions.

## Exact endpoint variant

Take all of B's actual tests, scales and admissible lists as in sequence-calculations.md. Enlarge the triple set by also admitting p=1. For a fixed enumeration of those triples set β_d=2^(−d)/C_d, and complete the mass-zero molecule quotient in

    N_end(m)=Σ_d β_d σ_d(m).

Call the completion W. The finite-seminorm, quotient, separability, exact-completion and duality arguments from the preceding note apply also to p=1. In particular its point map ζ_end:B_D→W is 1-Lipschitz and the correction coordinate map Q and radial lift K still exist. Thus the source's global onto absorption identity still holds for W. No assertion of no linear c0 in W is made; the source detector extraction needs a strictly smaller exponent and does not handle detection by a p=1 seminorm.

The question tested here is whether this endpoint automatically makes W Schur. It does not. The following construction produces a bounded weakly null sequence in W with norm bounded away from zero.

## A correction coordinate that is exactly affine along one segment

Fix i=1, λ=(1,1), and the band-zero label γ=(λ,0,*). Let e be the unit vector of the t_1 input coordinate in E⊂D. For ρ_1≤t≤1, the source schedule has θ_0^(Jλ)(rλ(te))=1, because rλ(te)=t. The current block x^λ is zero, its readout a_(1,1) is zero, and its predecessor readout is t_1=t. The band-zero vector is 1. Therefore the actual source formula gives

    fγ(te)=t,  ρ_1≤t≤1.                              (10)

Choose dyadic numbers a<b with ρ_1<a<b<1 and b−a=:L a negative power of 2. Such an interval exists since ρ_1<1. The finite set Iγ contains t_1. All other coordinates of te are zero.

Define the Lipschitz curve c(t)=ζ_end(te) for t in [a,b]. Its Lipschitz constant is ≤1. There is a bounded linear operator A:L1([a,b])→W with norm ≤1, determined on step functions by

    A(1_(u,v])=c(v)−c(u).

To justify this without a Banach-valued derivative, refine any step representation to a common interval partition. Telescoping proves independence of representation, and the Lipschitz estimate gives ||AΣ_j α_j1_(u_j,v_j]||≤Σ_j |α_j|(v_j−u_j). Complete the step functions in L1. For every source test u, the scalar curve t↦u(te) is Lipschitz, hence absolutely continuous; on all L1 functions,

    <u,Ag>=∫_a^b g(t) (d/dt)u(te) dt.              (11)

Only a scalar derivative is used. No derivative of c or of a Lipschitz Banach-space bijection is inferred.

## A weakly null family and its localized tests

For n large put h_n=L/2^n, which is dyadic, and

    r_n(t)=(-1)^floor((t−a)/h_n),  a≤t<b.

These Rademacher functions have ||r_n||_1=L and are weakly null in L1. Indeed, each fixed step function on an earlier dyadic partition has zero integral against r_n for all sufficiently large n. Such steps are dense in L1([a,b]); every L∞ test function is in L1 because the interval has finite measure, and ||r_n||∞=1 controls the approximation error. Thus all L∞ pairings tend to zero. Bounded linearity of A makes Ar_n weakly null in W.

Fix n sufficiently large that h=h_n<ℓ_0/2 and a is an integer multiple of h/8. For

    k=1,...,2^(n−2)−1,
    q_k=(a+(4k+1/2)h)e restricted to Iγ,

the center q_k belongs to the source's permitted grid Q_(Iγ,h). All other center coordinates are zero and the t_1 coordinate is an integer multiple of h/8. The single operation

    u_(n,k)=R_(q_k,h) fγ

is an actual member of T_1: its scale is dyadic, its operation count is one, and its scale sum h satisfies the strict budget <ℓ_0/2. B's operations lemma gives Lip(u_(n,k))≤3L0 with L0=4+12/1000. Its relative support is inside the finite-coordinate closed cylinder of radius h about q_k.

The centers have pairwise distance at least 4h, so these closed cylinders, and hence their relative supports, are disjoint. B's compatible-supports lemma applies on the convex set B_D. Every signed sum of this finite list has Lipschitz constant ≤3L0<13. Thus the whole list is admissible for the single fixed endpoint triple

    d*=(T_1,13,1),

independently of n and of the growing list length.

All support intervals on the selected segment lie inside [a,b]. Equation (10) gives, with q the scalar t_1 coordinate of q_k and z=t−q,

    u_(n,k)(te)=−z,                     |z|≤h/2;
                 −2z+2z|z|/h,          h/2≤|z|≤h;
                 0,                    |z|≥h.

Its scalar derivative is −1 on the inner interval and −2+4|z|/h on the two outer half-intervals. The inner interval [q−h/2,q+h/2] is exactly a positive r_n block [a+4kh,a+(4k+1)h]. Both outer half-intervals lie in negative r_n blocks. Therefore (11) yields the exact value

    <u_(n,k),Ar_n>=−2h.                            (12)

One can also obtain (12) without integrating the piecewise quadratic derivative: the inner contribution is −h, the total derivative integral over the support is zero, so the outer derivative integral is h; multiplication by r_n=−1 there contributes another −h.

Using admissibility of the entire list in the endpoint seminorm,

    ||Ar_n||_W ≥ β_(d*) σ_(d*)(Ar_n)
               ≥ β_(d*) · 2h(2^(n−2)−1)
               = β_(d*) (L/2−2h)
               ≥ β_(d*) L/4 >0                   (13)

for all sufficiently large n. This is a weakly null sequence that is not norm null. The specified p=1 endpoint completion W is not Schur.

## What this resolves, and what remains unpaid

The endpoint failure is concrete: a fixed class and one fixed admissibility constant detect diffuse mass across an increasing number of tiny tests. Each individual evaluation in (12) tends to zero, but the p=1 sum stays bounded below. Thus the original p'<p scalar extraction cannot simply be continued at p=1. The example realizes that obstruction using the actual source's band-zero correction, permissible grids, strict budgets, and local R-operations; it is not merely an abstract sequence-of-numbers analogy.

This does not prove that every possible detecting test has small pairing on Ar_n, and such a claim is unnecessary. The displayed weakly null sequence and the lower bound (13) already disprove the Schur property of this exact endpoint. It also does not classify W's linear subspaces or decide whether it contains c0.

For a genuinely stronger Schur-space absorption construction, one would need a new way to retain the identity QK=g−P and global Lipschitz point-map bounds while preventing this diffuse endpoint mechanism. No such compatible construction is established here. Applying Kalton's nontrivial gauge gives a Schur free space, but its small-distance modulus ω(t)/t→∞ loses the required global linear upper bound; that known construction supplies uniform absorption only. Applying Source324 A's complete-continuity theorem would require a bounded factorization of a different Hilbert-valued correction through this selected molecule norm; the source provides no such factorization. Moreover its free space already contains a linear Hilbert copy by the separable lifting theorem, so its WSC input is not a Schur substitute.

The broader Schur extension is left as an unfrozen research direction, not an asserted theorem or a renamed failed historical target. The scope of I88 S88 (coupled AP/no-BAP absorption) and all excluded targets remains untouched.
