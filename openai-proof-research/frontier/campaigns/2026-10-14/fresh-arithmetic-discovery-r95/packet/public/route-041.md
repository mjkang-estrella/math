# Main direction: source041 projective-space bases, nonprojective Kähler case

Status: screened, not frozen, no nominee. The target below was considered as a candidate and rejected before any freeze because every integrated operation it needs is already paid. Nothing here is offered as a proved new result.

## Source scope (read in the pinned bodies)

- Projective-Space-Bases `thm:main` (01-introduction.tex, lines 59–71). $X$ is a compact IHS Kähler manifold of dimension $2n$. The map $f:X\to B$ is a *projective* surjective holomorphic morphism with connected fibers onto a *normal projective* variety $B$ of dimension $n$, and all fiber components are $n$-dimensional and Lagrangian. Conclusion: $B\simeq\mathbb P^n$. Lines 73–75 note that projectivity of $f$ and $B$ makes $X$ projective.
- Strong SYZ `cor:projective-base` (introduction.tex, lines 69–80) applies the base theorem only under the extra hypothesis that $X$ is projective. Strong SYZ `thm:main` itself works on any compact IHS Kähler manifold.
- Projective-Space-Bases introduction (lines 11–19) cites Greb–Lehn Proposition 2.2 (the base of any fibration of a compact IHS Kähler manifold is normal projective of dimension $n$, with Lagrangian fiber components) and Greb–Lehn Theorem 1.1 (smooth base implies $\mathbb P^n$ in the Kähler case).

The unrestricted Kähler statement, with singular base and nonprojective total space, is therefore not stated in either companion.

## Candidate considered (never frozen)

> Let $X$ be a compact IHS Kähler manifold of dimension $2n$, $n\ge1$, and let $f:X\to B$ be a proper surjective holomorphic map with connected fibers onto a normal complex space with $0<\dim B<2n$. Then $B\simeq\mathbb P^n$.

## Why it was not frozen: every operation is paid

Feasibility sketch, written mentally before reading the source paragraph cited in route (b) below:

1. **Base properties.** Greb–Lehn 1303.3919v2, Proposition 2.2 (read): $B$ is a normal projective variety of dimension $n$, and every fiber component is Lagrangian. Fix a very ample $H$ on $B$ and set $e=c_1(f^*H)$.
2. **Moving to a projective member while keeping the base.** There are two routes.
   - (a) **Matsushita route.** Matsushita 0903.2098v2 (read) states Theorem 1.2 and Corollary 1.3 for a compact Kähler irreducible symplectic $X$ with a Lagrangian fibration over a projective $B$; projectivity of $X$ is not assumed. They give a family $\mathcal X\to U$ over the $e$-Hodge hypersurface and a relative morphism to $\mathbb P(\pi_*\mathcal L)$. Take the relative Stein factorization $\mathcal X\to\mathcal B\to\mathbb P$.
     - The local-product step in the proof of source `def:fixed-base` (07-deformation.tex: setup on lines 84–136, local product on lines 137–178) is local. It uses a smooth slice, a finite map to the normal germ $(\mathcal B,b)$ and normalized trace derivations, and never uses projectivity of the central fiber. It gives $(\mathcal B,b)\simeq(B,b)\times(U,0)$ at every central point. Only the globalization step (lines 179–202) uses $H^1(B,T_B)=0$, and it is not needed here.
     - Projective periods are dense in the $e$-Hodge hypersurface. For an integral class $\alpha$ near $N\kappa$ with $q(\alpha)>0$, the hypersurface $\alpha^\perp$ meets every neighbourhood, because $q(\cdot,\kappa)$ does not vanish on $e^\perp\cap(\operatorname{Re}\sigma,\operatorname{Im}\sigma)^\perp$. Huybrechts' projectivity criterion then makes those members projective. Greb–Lehn cite Fujiki Theorem 4.8(2) for the same density.
     - At a projective member $X_t$, the map $X_t\to\mathcal B_t$ is projective, and $\mathcal B_t$ is normal and projective (it is finite over its image in $\mathbb P$). Source `thm:main` gives $\mathcal B_t\simeq\mathbb P^n$. The local products then make $B$ smooth, and Greb–Lehn Theorem 1.1 gives $B\simeq\mathbb P^n$.
   - (b) **Degenerate-twistor route.** The source introduction (lines 149–158, read late) already records that Verbitsky's degenerate-twistor construction keeps the Lagrangian fibration holomorphic over the *original* base along a complex line (Verbitsky 2015, Theorem 1.10). Soldatenkov–Verbitsky 2025 (Section 2.2, Theorem 3.1, Corollary 3.3) treat normal analytic bases and compact IHS fibrations. The periods along that line are $[\sigma]+te$. For an integral $\alpha$ with $q(\alpha)>0$ and $q(\alpha,e)\neq0$, the parameter $t_\alpha=-q(\alpha,\sigma)/q(\alpha,e)$ makes $\alpha$ a $(1,1)$-class, and such $t_\alpha$ accumulate at $0$. A projective member then has the same base $B$, and source `thm:main` applies directly.
3. **Conclusion of the check.** Either route is the Greb–Lehn template (deform to projective members, apply the projective theorem, return), with source041 in place of Hwang. The fixed-base insert that the singular case needs is supplied by the source itself, both by the trace-derivation local product and by the cited degenerate-twistor and Soldatenkov–Verbitsky results. No unpaid compatibility operation was identified. Under the brief (routine composition and classical compiler applications earn no count), freezing it would lower the substantiality threshold.

## Limits

- The Verbitsky 2015 and Soldatenkov–Verbitsky 2025 primaries were *not* acquired or read. Route (b) relies only on the source's own description of them. Route (a) uses only primaries that were read (Matsushita, Greb–Lehn), plus the pinned source body.
- The codimension-one multiple-fiber part of the companion statements (Kim–Oguiso–Shinder, Kamenova–Verbitsky) was not examined in the Kähler setting.
- Campana 1712.01902v2 (read) gives *local* projectivity of $f$ for Kähler $X$. Global projectivity of $f$ over projective $B$ would make $X$ projective, so the source hypothesis fails exactly in the nonprojective case. This only confirms the scope gap; it closes nothing.
- The sketch above is a feasibility check and was not independently verified. It is not an author proof.
