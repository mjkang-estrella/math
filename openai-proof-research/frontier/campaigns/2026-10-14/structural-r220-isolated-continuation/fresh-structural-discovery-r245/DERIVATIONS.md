# R245 prefreeze mathematical derivations

This is a discovery notebook, not a frozen nominee or a correctness/contribution decision. The immutable Source370 proof and its operative operations are assumed true. All statements below are derived at their written scope; no literature-priority claim is made. Runtime: Codex / GPT-6 Astra / xhigh / standard speed, serviceTier default. Only the parent adopts grades or counts.

## 1. Scaling and the three product regimes

Write the equations as -Δu=|x|^A a(x)v^p and -Δv=|x|^B b(x)u^q, where p,q>0 and the dimension is n≥2. For the coefficient classes considered here, 0<m≤a,b≤M, and the solutions are strictly positive, continuous at zero and classical off zero (or distributional with the regularity explicitly stated below).

For u_R(x)=R^αu(Rx), v_R(x)=R^βv(Rx), direct differentiation gives

-Δu_R=R^(α+2+A-pβ)|x|^A a(Rx)v_R^p,
-Δv_R=R^(β+2+B-qα)|x|^B b(Rx)u_R^q.

Thus pβ=α+2+A and qα=β+2+B. Only when pq≠1 may one solve

α=[2+A+p(2+B)]/(pq-1), β=[2+B+q(2+A)]/(pq-1).

Spherical flux at the origin is zero, by boundedness and monotonicity, exactly as in Source370 Lemma reductions. Positive comparable coefficients give the same contradictions if n=2 or A≤-2 or B≤-2. Hence an entire positive origin-continuous pair necessarily has n≥3 and A,B>-2. The distributional extension has no point mass, since the cutoff errors are O(ρ^(n-2)) and the sources are integrable. Newton potential domination follows by mollification and spherical averaging.

For m_u(R)=inf_(B_R)u and m_v(R)=inf_(B_R)v, potential domination and the lower coefficient bound give m_u≥cR^(2+A)m_v^p and m_v≥cR^(2+B)m_u^q. Therefore

m_u(R)^(1-pq)≥c R^[2+A+p(2+B)].

If pq<1 the left side is bounded by u(0)^(1-pq); if pq=1 it is 1. Both contradict R→∞. No singular scaling exponents are used in either case. When pq>1, α,β>0.

Let θ=1/(q+1), τ=1/(p+1), and γ=θ(n+B)+τ(n+A)-(n-2). Then

γ=(1-θ-τ)(α+β+2-n), 1-θ-τ=(pq-1)/[(p+1)(q+1)]>0.

## 2. Paid unweighted doubling transfer, including sublinear powers

Fix n≥3, p,q>0, pq>1 and n/(p+1)+n/(q+1)>n-2. Set α0=2(p+1)/(pq-1), β0=2(q+1)/(pq-1). For a nonnegative solution in an arbitrary proper domain Ω of -Δu=v^p, -Δv=u^q, set M=u^(1/α0)+v^(1/β0). Both summands have scaling degree one. The inadmissible sum u+v is not used.

The doubling lemma is proved by iteratively replacing a point with a point where M more than doubles at distance ≤k/M. If the iteration did not terminate, the distances sum to at most 2k/M(initial), a Cauchy sequence remains a positive distance from the excluded boundary, and local boundedness contradicts M→∞. Starting from a violation M(y)dist(y,∂Ω)>2k yields x with M(x)dist(x,∂Ω)>2k and M≤2M(x) on B_(k/M(x))(x).

With λ=1/M(x), U(z)=λ^α0 u(x+λz), V(z)=λ^β0 v(x+λz), the equations are unchanged, U(0)^(1/α0)+V(0)^(1/β0)=1, and the same sum is ≤2 on B_k. On fixed balls the right sides are uniformly bounded. Interior W^(2,t) estimates for arbitrary finite t give C^(1,η) convergence on smaller balls. Uniform convergence of nonnegative functions implies uniform convergence of their positive powers, also for powers below one. The limiting right sides are locally Hölder, with exponent reduced by min(1,p,q), so the limit is classical. No Lipschitz estimate for s↦s^p at zero is needed.

The limit is nonnegative and not the zero pair. A nonnegative superharmonic function that vanishes at an interior point is identically zero. If one component were identically zero, its equation would force the other to be zero. Thus both limiting components are strictly positive, contradicting Source370's unweighted theorem. This proves M≤C/dist(x,∂Ω). Local elliptic estimates on a ball of radius proportional to the boundary distance also give |∇u|≤C dist^(-α0-1), |∇v|≤C dist^(-β0-1).

For fixed positive constants c,d, -ΔU=cV^p, -ΔV=dU^q is reduced to unit coefficients by multiplying U by (c d^p)^(1/(pq-1)) and V by (d c^q)^(1/(pq-1)). This explicitly preserves strict positivity. Uniform constants on a compact parameter set separated from pq=1 and the critical hyperbola follow by the same contradiction argument; this supplies no effective modulus as the gap tends to zero.

The actual classical comparison is PQS, section 5 Lemma 5.1 and section 7 proof of Theorem 4.3, with their p,q>1 restriction replaced here only by the above direct compactness/positivity argument. This is a paid classical composition.

## 3. Annular freezing and the correct weighted rate

Assume the unweighted strict hyperbola condition in section 2 and A,B>-2. For an origin-punctured solution of the homogeneous weighted system, fix x≠0 and R=|x|/2 with B_R(x) inside the domain. Let U(y)=R^αu(x+Ry), V(y)=R^βv(x+Ry). Then on B_1,

-ΔU=|e+y|^A V^p, -ΔV=|e+y|^B U^q, e=x/R, |e|=2.

The coefficients on B_1 are positive, uniformly bounded above/below and have uniform first-derivative bounds as e varies on the sphere of radius 2. A contradiction to an interior bound allows doubling with exponents α0,β0, not α,β. Its new scales λ_k→0 make |e_k+x_k+λ_k z|^A and the B weight converge locally uniformly to positive constants. The transfer in section 2 then applies. Thus u(x)≤C|x|^-α, v(x)≤C|x|^-β, with the corresponding gradient rates. This reproduces Phan's annulus argument in its full compatible unweighted Liouville range.

The weighted hyperbola alone does not justify this step. For example n=5,p=q=4,A=B=3 has γ=1/5>0 but n/(p+1)+n/(q+1)=2<n-2=3. A blow-up whose scale divided by its distance from zero tends to zero has a constant-coefficient unweighted limit; Source370 permits that limit in this example.

## 4. Gradient-free small relative coefficient perturbations in the intersection of the two subcritical regions

Here is the complete classical composition, retained to avoid presenting it as an unpaid operation. Fix n≥3,p,q>0,pq>1,A,B>-2 such that BOTH γ>0 and n/(p+1)+n/(q+1)>n-2. Then there exists ε0>0, depending on these fixed parameters, for which no strictly positive entire, continuous, distributional pair solves

-Δu=|x|^A a(x)v^p, -Δv=|x|^B b(x)u^q,

with measurable coefficients |a-1|≤ε0, |b-1|≤ε0 almost everywhere. The functions may be taken W^(2,t) locally off zero for all finite t; this follows from local boundedness and the equations. No coefficient derivative or equicontinuity is assumed.

First there exist ε1>0,C<∞ such that the annular bound in section 3 holds for every such coefficient pair with oscillation ≤ε1. Otherwise, for each integer k select coefficient errors ≤1/k and an annular solution violating the bound by k. Perform the annulus rescaling and doubling as in section 3. In the doubled coordinates the modulation tends to 1 in L∞, irrespective of its frequency, while the smooth radial weight freezes. The bounded normalized solutions converge in C^1 locally using W^(2,t) estimates; the right sides converge in L^t, which suffices to pass the equations. The limit is the same positive constant-coefficient solution ruled out in section 2. This gives ε1,C, not an explicit value.

Suppose now the claimed entire nonexistence failed for every ε0. Choose entire pairs with errors ε_k→0, all ≤ε1. Define H_k(R)=R sup_(|x|≤R)[u_k(x)^(1/α)+v_k(x)^(1/β)]. It is continuous, tends to zero as R↓0 and to infinity as R→∞, since u_k(0)>0. Choose R_k with H_k(R_k)=1 and dilate about zero. On B_1 the resulting weighted-degree-one sum is ≤1 and its supremum is 1. On |x|≥1/2 the uniform annular bound from the previous paragraph bounds both components on every fixed ball. Thus the normalized pairs are locally uniformly bounded on all R^n.

For the origin, choose t>n/2 such that tA>-n and tB>-n whenever A or B is negative. Such t exists precisely because A,B>-2. The right sides are uniformly L^t on every fixed ball and converge there to |x|^A V^p, |x|^B U^q by dominated convergence plus the vanishing L∞ modulation. Interior W^(2,t) estimates give uniform C^(0,η) compactness across zero. Away from zero they give C^1 compactness and the limiting smooth coefficient equations bootstrap to C^2. Normalization gives a nonzero limit, because maximizing points in closed B_1 have a convergent subsequence and convergence is uniform there. The distributional strong minimum principle (or positive Newton-potential comparison on balls) makes both components strictly positive everywhere, including zero. Source370's weighted theorem now contradicts γ>0.

The proof uses no boundary geometry: the domains after each normalization exhaust the whole space. It gives no Dirichlet boundary estimate, no quantitative ε0, and no uniform statement near either hyperbola. For pq≤1, comparable-coefficient nonexistence already follows from section 1.

## 5. A full derivative-controlled extension in the weighted-only region

Fix n≥3,p,q>0,pq>1,A,B>-2. Let a,b∈C^1(R^n\{0}) with 0<m≤a,b≤M, and assume

|x|(|∇log a(x)|+|∇log b(x)|)≤L,
x·∇log a(x)≥-εA, x·∇log b(x)≥-εB,
Γ:=γ-εB/(q+1)-εA/(p+1)>0,

where εA,εB≥0. There is no positive entire origin-continuous classical-off-zero pair for these equations. This is a direct extension of the paid source pressure construction, not a nominee.

Details of the full source interfaces follow. Set f=|x|^B b u^q, g=|x|^A a v^p. The origin extension and Newton potential representation in source section 2 use comparability only. A positive harmonic remainder is constant. On B_1 the potential lower bound gives M_f≥c M_g^q and M_g≥c M_f^p, so pq>1 bounds both masses independently of the solution. Under origin dilation the coefficients become a(Rx),b(Rx), which obey the SAME m,M,L,εA,εB bounds. Hence

∫_(B_R)f≤C R^(n-2-β), ∫_(B_R)g≤C R^(n-2-α).

The positive harmonic constants vanish because a positive constant component would force source growth R^(n+B) or R^(n+A), inconsistent with these bounds. Summing annuli proves the same tail bound ∫_(|x-y|≥ℓ)K(x-y)(f+g)(y)dy≤Cℓ^(2-n), x∈B_2, 0<ℓ≤1, and ∫_(B_4)(f+g+u+v)≤C.

Use exactly the source cutoffs m0=n+3,k=n(m0+1),N=k+n+2, d=min(1,(2-|x|)_+), η=[(1-(|x|-1)_+^3)_+]^N, w=-x·∇η and X=xη. Put E_f=∫ηfu,E_g=∫ηgv,E=E_f+E_g and dπ=f(x)g(y)K(x-y)dxdy. The proof of source localization is unchanged: it uses only these potential marginals, cutoff derivatives and the just-proved mass/tail bounds. It yields

|E_f-E_g|+|Q|≤εE+C_ε,
Q=∫[Φ-η(x)+w(x)D(x,y)]dπ.

The exact modified virial identity is

θ∫η[n+B+x·∇log b]fu + τ∫η[n+A+x·∇log a]gv -θW_f-τW_g
=(n-2)∫Φdπ.

The origin boundary terms are O(ρ^(n+B)) and O(ρ^(n+A)), including bounded modulation, and vanish. The kernel-gradient convergence proof is unchanged because the source on a ball of radius |x|/2 is bounded by a solution-dependent constant times |x|^A or |x|^B.

At a retained f-layer endpoint z, u(z)=[t/(|z|^B b(z))]^(1/q). On 1≤|z|≤2 the logarithmic gradient of (|z|^B b(z))^(-1/q) is bounded by a constant depending on B,q,L. Thus on an interval of length ≤2δ inf d the source weighted-endpoint error remains ≤Cδd(x)u(x). The analogous statement holds for g. The layer identity remains exactly ∫_0^f[u-(t/(|x|^B b(x)))^(1/q)]dt=fu/(q+1).

Every other pressure operation is identical: cap normalization E_e h_e=w; near/far cap mismatch; polar probability of long intervals ≤C/(tℓ^n); high levels ≥P d^-k; low levels bounded by CP using ∫u; interval-pair inequality with weights constant on each retained interval; Tonelli BEFORE finite subtraction; and the parameter order κ small, then δ small, then P large. In particular

θW_f+τW_g≤(n-2)∫wD dπ+εE+C_ε.

The virial lower bound then gives c1 E_f+c2 E_g≤(n-1)εE+C_ε with c1=θ(n+B-εB)-(n-2), c2=τ(n+A-εA), c1+c2=Γ. Localization replaces E_f-E_g by an arbitrarily small relative error. Absorb it to obtain E≤C uniformly over the whole coefficient class.

For each R the dilated solution and coefficients stay in that class, and

∫_(B_1)[|x|^B b(Rx)u_R^(q+1)+|x|^A a(Rx)v_R^(p+1)]
=R^(α+β+2-n)∫_(B_R)(fu+gv).

Γ>0 implies γ>0 and α+β+2-n>0. The right side diverges as R→∞ since the energy on B_1 is fixed and strictly positive, contradicting the uniform bound. This completes the extension through all coefficient, endpoint, and scaling interfaces.

The coefficient class is nonempty and genuinely nonhomogeneous. For instance n=5,p=4,q=2,A=3,B=1 gives pq=8, α=17/7,β=13/7,γ=3/5, while the unweighted gap is -1/3. The smooth radial functions a(x)=exp(c sin(log(1+|x|^2))) and b(x)=exp(c cos(log(1+|x|^2))) satisfy m=e^-c,M=e^c, each |x||∇log|≤2c and each radial drift ≥-2c. Thus Γ≥3/5-2c(1/3+1/5)>0, for example c=1/20. Neither coefficient is homogeneous, and they keep oscillating at large logarithmic radii. Constant-on-rays positive angular factors may also be inserted, increasing L without changing the radial drift inequalities. No nonexistent free parameter was used.

## 6. Explicit obstruction to removing coefficient restrictions altogether

Let κ>0, p,q>0,pq>1 and put A=B=κ-2, α=κ(p+1)/(pq-1), β=κ(q+1)/(pq-1). Assume 0<α,β<n-2. Set

u(r)=(1+r^κ)^(-α/κ), v(r)=(1+r^κ)^(-β/κ),
a(r)=α[(n+κ-2)+(n-α-2)r^κ]/(1+r^κ),
b(r)=β[(n+κ-2)+(n-β-2)r^κ]/(1+r^κ).

Direct differentiation gives -Δu=r^(κ-2)a(r)v^p and -Δv=r^(κ-2)b(r)u^q. Both coefficients are bounded above and below by positive constants. Both functions are strictly positive and continuous at zero, with no point mass. If κ is an even positive integer they are smooth everywhere.

Take n=5,κ=4,p=4,q=3. Then A=B=2, α=20/11,β=16/11, α+β=36/11>3 and γ=3/20>0. In this concrete example

u=(1+r^4)^(-5/11), v=(1+r^4)^(-4/11),
a=(20/11)[7+(13/11)r^4]/(1+r^4),
b=(16/11)[7+(17/11)r^4]/(1+r^4).

It is an exact positive smooth entire pair for comparable nonhomogeneous coefficients in the strictly weighted-subcritical region. It does not contradict Source370, whose coefficients are exactly the homogeneous powers. It does not contradict section 5, whose drift restriction fails. It prevents replacing the restrictions there by mere positive upper and lower coefficient bounds. This elementary profile construction is already suggested by the supersolution examples in Phan's introduction and is not offered as novel.

For C=n+κ-2 and D=n-α-2, the maximal negative radial logarithmic drift of a is

sup_r[-r(log a)'(r)]=κ(√C-√D)/(√C+√D),

obtained at r^κ=√(C/D). This supplies an exact measure of the example's departure from the drift-controlled class, not a sharp threshold theorem.

## 7. Origin limits, singular weak solutions, and Kelvin bookkeeping

For punctured solutions, the rates u≤Cr^-α, v≤Cr^-β imply source integrability near zero only when α<n-2 and β<n-2, since |x|^A v^p has radial integral exponent n-1+A-pβ=n-3-α. A gradient bound gives vanishing puncture flux only under the corresponding strict inequality. At equality a logarithmic divergence or a point mass requires a separate analysis.

Even integrability and zero point mass do NOT give continuity. Let α,β∈(0,n-2) be the weighted scaling exponents, Lα=α(n-2-α),Lβ=β(n-2-β). Define

C=(Lα Lβ^p)^(1/(pq-1)), D=(Lβ Lα^q)^(1/(pq-1)).

Then u=C r^-α,v=D r^-β is an exact positive classical punctured solution. The weighted sources are locally integrable, the fluxes vanish as r↓0, and the cutoff boundary errors O(r^(n-2-α)),O(r^(n-2-β)) show it solves the equations distributionally across zero with no point masses. It is nevertheless unbounded. These examples can lie in the strictly weighted-subcritical region α+β>n-2. E.g. n=3,p=q=4,A=B=0 gives α=β=2/3 and C=D=(2/9)^(1/3). This rules out silently applying the source theorem to arbitrary nonnegative distributional limits.

For the Kelvin transform U(x)=|x|^(2-n)u(x/|x|^2), V similarly, the transformed weights are

A*=p(n-2)-(n+2)-A, B*=q(n-2)-(n+2)-B.

The transformed scaling exponents are α*=n-2-α, β*=n-2-β. Continuity at the new origin demands the appropriate full asymptotic behavior of |y|^(n-2)u(y), not simply a scale-invariant estimate. A finite nonzero common-direction limit gives strict positivity at the new origin; a bounded but direction-dependent profile does not prove continuity. No Kelvin theorem is claimed beyond this calculation.

## 8. Unpaid direction carried to its actual obstruction

The remaining attempted extension is frequency-independent small RELATIVE L∞ coefficient perturbations under the WEIGHTED hyperbola alone, including parameters outside the unweighted subcritical region. Section 4 closes this completely on the intersection of the two regions; section 5 closes a different, derivative-controlled class even in the weighted-only region. Neither proves the amplitude-only weighted-only extension.

A local rescaling at points x_j with scale λ_j and λ_j/|x_j|→0 freezes the power weight after the correct constant-amplitude renormalization. The possible limiting system is the unweighted supercritical or critical system, where the paid radial existence theorem provides positive entire solutions. When |x_j|/λ_j stays bounded, the weighted-scale normalization retains |z+ξ|^A,|z+ξ|^B; continuity at the offset pole needs uniform bounds and the L^t argument from section 4. No such global bound has been obtained in the weighted-only case. When |x_j|/λ_j→0 the pole is centered in the limit; this is not the same as the first regime. With unweighted normalization rather than weighted normalization, the coefficients may diverge or vanish; this cannot be ignored.

The alternative attempt is to remove coefficient derivatives from the source virial identity by integration by parts. Writing a=1+h, |h|≤ε, transfers derivatives from h to η|x|^A v^(p+1), and creates a term controlled only by ε∫η|x|^A v^p |x·∇v| (and its companion). Source masses and E do not by themselves control the required absolute gradient interaction by CE.

A concrete test of that proposed intermediate estimate: take smooth nonnegative unit-mass bumps f_h,g_h of radius h/10 centered at x0 and x0+h e respectively, with x0 fixed inside B_1 away from zero and e parallel to x0. Then E_h=∫∫K(x-y)f_h(x)g_h(y)dxdy is comparable to h^(2-n), while the absolute directional-gradient interaction is comparable to h^(1-n). Hence its ratio to E_h diverges like 1/h. The masses, local L^1 potential bounds and truncated-potential estimates remain uniformly bounded. For α,β<n-2 the source centered mass envelopes also hold uniformly because both supports stay in a fixed annulus. These bumps are NOT asserted to solve the nonlinear equations; they show only why the proposed estimate cannot follow from those source-control inputs alone. The signed unperturbed virial cancels the leading singularity through X(x)-X(y); unrelated rapidly varying multipliers destroy that available cancellation.

What remains unproved is an additional PDE-specific estimate recovering this cancellation for merely small L∞ modulation, or a construction of actual solutions showing that such robustness fails in the weighted-only region. The exact smooth profiles in section 6 rule out unrestricted comparability but not arbitrarily small relative perturbations. No claim is frozen, narrowed from an old target, or submitted for a grade. This is PREFREEZE/no nominee.


## 9. Complete independent radial existence comparison

This fills the local-shooting interface of Bidaut-Véron–Giacomini's actual argument, without importing an unproved regularity assertion when a power is below one. Assume n≥3,A,B>-2,p,q>0 and γ≤0. The joint assumptions force pq>1: since n+A,n+B>n-2>0, one obtains 1/(p+1)+1/(q+1)<1, hence pq>1.

For initial values U(0)=1,V(0)=t>0, solve the radial integral equations

U(r)=1-∫_0^r s^(1-n)∫_0^s ρ^(n-1+A)V(ρ)^p dρ ds,
V(r)=t-∫_0^r s^(1-n)∫_0^s ρ^(n-1+B)U(ρ)^q dρ ds.

On a small ball of continuous functions around these strictly positive initial values, the powers are locally Lipschitz, and each integral operator has norm bounded by a constant times r^(2+A) or r^(2+B). Contraction gives local existence, uniqueness and continuous dependence up to any time while both profiles stay positive. Both profiles strictly decrease, remain bounded, and continue until a component first reaches zero or r→∞. On a finite positive interval their derivatives are controlled by the integral formulas, so there is no other obstruction to continuation.

For t small, choose r_t=K t^(1/(B+2)). While positive, U(r)≥1-C t^p r^(A+2). Thus U≥1/2 up to r_t for sufficiently small t, since p+(A+2)/(B+2)>0. In turn V(r)≤t-c r^(B+2); choose K with cK^(B+2)>1. V must reach zero before r_t, while U remains positive. For t large, choose r_t=K t^(-p/(A+2)). The estimate V(r)≥t-C r^(B+2) gives V≥t/2 up to r_t. Then U(r)≤1-c t^p r^(A+2), so U reaches zero first for K sufficiently large. These are nonempty exit sets of initial ratios.

Each one-component exit set is open. At such an exit the vanishing component has strictly negative radial derivative by its flux formula, and the other component has a positive value. Continuous dependence on a slightly earlier compact positive interval, the negative flux, and a uniform derivative bound for the positive companion guarantee the same ordering for nearby initial ratios. This argument does not require Lipschitz continuity of a positive power at zero, nor continuation through a negative component.

Define

H(r)=r^n[U'V'+r^B U^(q+1)/(q+1)+r^A V^(p+1)/(p+1)]
+r^(n-1)[(n+A)/(p+1) VU'+(n+B)/(q+1) UV'].

Direct differentiation using the radial equations gives H'(r)=γ r^(n-1)U'V'. The origin estimates U'=O(r^(A+1)),V'=O(r^(B+1)) imply H(0)=0: even the product term has exponent n+A+B+2>n-2>0. Since U',V'<0 and γ≤0, H≤0 while the pair stays positive. A simultaneous finite zero at R would instead give H(R)=R^n U'(R)V'(R)>0. It is impossible.

If every t>0 had a finite exit, the connected interval (0,∞) would therefore be the disjoint union of the two nonempty open one-component exit sets. This is impossible. A remaining ratio gives a positive global radial pair with strictly positive initial values and the required origin continuity. This proves the complementary existence comparison at its exact compatible scope; uniqueness and the detailed asymptotics from the original paper are not claimed. The scalar subcases and parameter endpoints have not been substituted for the coupled argument.

## 10. The amplitude-only radial reduction actually closes

As an internal comparison, not a replacement nominee, the weighted-only amplitude-perturbation question closes for radial profiles. Fix n≥3,p,q>0,pq>1,A,B>-2,γ>0. There is ε_rad>0 such that positive origin-continuous RADIAL entire pairs cannot solve the equations with radial measurable modulations |a-1|,|b-1|≤ε_rad. This is another paid compactness composition, not the unrestricted attempted target in section 8.

If false, take errors ε_j→0 and radial pairs. Dilate with the weighted exponents to make U_j(0)=1. The modulations remain within ε_j of 1 at every radius. Set t_j=V_j(0). The small- and large-ratio exit estimates in section 9 use only 1/2≤a,b≤3/2, and show uniformly that an entire pair cannot have t_j→0 or t_j→∞. Thus c≤t_j≤C. Radial superharmonicity gives 0<U_j≤1, 0<V_j≤C everywhere. The integral equations give, on every fixed interval,

|U_j'(r)|≤C_R r^(A+1), |V_j'(r)|≤C_R r^(B+1).

Their integrals at zero are finite since A,B>-2, yielding equicontinuity there, and ordinary equicontinuity away from zero. A diagonal subsequence converges uniformly on compact radial intervals. The integral formulas pass to the limit by dominated convergence, because ε_j→0 and the powers are continuous on bounded nonnegative ranges. The limit is an entire nonnegative radial homogeneous-coefficient solution with U(0)=1,V(0)≥c. If either profile first vanished, its strictly negative flux at that radius would force it negative just beyond, contradicting the nonnegative global limit. Thus both are strictly positive, contrary to Source370. The proof provides ε_rad non-effectively.

This identifies the missing operation more concretely: radial monotonicity supplies global pointwise compactness from the two origin values, without an unweighted translated-limit theorem. No corresponding nonradial control has been established. A spherical mean bound alone cannot replace that pointwise control.

## 11. Exact translated-normalization formulas

For arbitrary positive amplitudes c_j,d_j, write U_j(z)=c_j u_j(x_j+λ_j z), V_j(z)=d_j v_j(x_j+λ_j z). Then the first rescaled coefficient is

c_j λ_j^2 d_j^(-p) |x_j+λ_j z|^A a_j(x_j+λ_j z),

and the second is d_j λ_j^2 c_j^(-q)|x_j+λ_j z|^B b_j(x_j+λ_j z). These formulas govern every limit below.

If ξ_j=x_j/λ_j→ξ∈R^n, choose c_j=λ_j^α,d_j=λ_j^β. The coefficients are |z+ξ_j|^A a_j(...), |z+ξ_j|^B b_j(...). If a_j,b_j→1 in L∞ and the solution components are uniformly locally bounded, choose t>n/2 with tA,tB>-n when needed. Translation continuity in L^t for the singular powers, and uniform boundedness of their L^t norms on compact sets, give C^0 compactness of the solutions and convergence of the right sides. Thus the limit is the offset weighted equation, continuous at its pole. The case ξ=0 is included. These are CONDITIONAL compactness implications; they do not supply the required solution bounds in section 8.

If r_j=|x_j| and λ_j/r_j→0, choose

c_j=λ_j^α0 r_j^[(A+pB)/(pq-1)],
d_j=λ_j^β0 r_j^[(B+qA)/(pq-1)].

Then the two power coefficients become (|x_j+λ_j z|/r_j)^A and (|x_j+λ_j z|/r_j)^B. They tend locally uniformly to 1. With a_j,b_j→1 in L∞ and locally bounded normalized solutions, the limit is the unweighted system. One cannot assume that these locally bounded solutions exist merely from the choice of c_j,d_j; the annular doubling argument supplies that property only in its proved regime.

If instead one uses weighted amplitudes λ_j^α,λ_j^β while |ξ_j|→∞, the two coefficients have leading factors |ξ_j|^A and |ξ_j|^B. Independently, they diverge for positive weight, vanish for negative weight, or stay one for zero weight. The unweighted constant-coefficient limit therefore requires the additional amplitude factors just displayed. An arbitrary mismatched normalization could leave a semitrivial or degenerate limiting system; it is never used as a source Liouville contradiction here.

No boundary rescaling is asserted. PQS section 7's half-space argument invokes a separate bounded half-space monotonicity/dimension-reduction theorem. That external ingredient was not independently read in this round. Neither odd nor even reflection is used, and no bounded-domain a priori theorem is inferred from the interior proof.


## 12. The finite-energy inner-cutoff interface closes as well

A final compatible source composition can be completed without assuming continuity at the singular point. This is recorded as a proved proof-interface extension, with no claim that the local hypotheses define a genuinely larger class than classical removability theory, and no contribution nomination.

Fix the parameters and coefficients of section 5 (the homogeneous case is included). Suppose u,v∈L^1_loc(R^n), strictly positive almost everywhere, and u,v∈C^2(R^n\{0}); suppose

f=|x|^B b u^q, g=|x|^A a v^p∈L^1_loc,
-Δu=g, -Δv=f in D'(R^n),
fu+gv∈L^1_loc(R^n).

In particular the distributional equations carry NO point masses. Under Γ>0 such a pair does not exist. Assigning an arbitrary value at zero has no effect. Only this precise weak class is considered.

Mollification of the nonnegative superharmonic distributions gives the spherical-potential inequality K*g≤u and K*f≤v almost everywhere. Fubini is valid because K*g≤u∈L^1_loc and K*f≤v∈L^1_loc. The differences u-K*g and v-K*f are nonnegative harmonic distributions, hence constants. Potentials are finite and C^1 off zero: the sources are locally C^1 there; near zero the fixed off-zero kernel and its gradient are bounded, and the tails are dominated by a finite potential value. Thus the representations are pointwise off zero. The centered source mass inequalities, their dilation, vanishing of the harmonic constants, the tail estimates, and the local L^1 potential bounds from section 5 use no value or boundedness at zero. They all remain valid. The assumed local interaction energy makes both marginals finite on B_2.

Here is the only changed virial justification. Choose a smooth radial ξ with ξ=1 on B_1 and ξ=0 outside B_2, and let X_ρ(x)=X(x)[1-ξ(x/ρ)], where X=xη. For each fixed ρ>0 this vector field is supported away from zero, so the usual pointwise integration by parts and differentiated Newton potentials are legitimate. Its Lipschitz norm is bounded independently of ρ, since |x|·|∇ξ(x/ρ)|/ρ≤C on its transition annulus. Therefore

Φ_ρ(x,y)=[X_ρ(x)-X_ρ(y)]·(x-y)/|x-y|^2

is bounded by C[1_(B_2)(x)+1_(B_2)(y)] and converges to Φ off the negligible sets at zero and the diagonal. This dominating function is integrable against π by the local interaction-energy assumption. Dominated convergence passes the symmetrized kernel integral to the limit. There is no need to bound the two unsigned, unsymmetrized gradient interactions separately uniformly in ρ.

On the integration-by-parts side, the extra term involving x·∇ξ(x/ρ) is bounded in absolute value by C∫_(B_(2ρ)\B_ρ)(fu+gv), which tends to zero by absolute continuity of the integral. The remaining terms converge by the same local energy integrability and the bounded logarithmic coefficient drifts. This proves exactly the modified virial identity in section 5.

Localization uses the finite energy marginals, source masses and tails, all already available. Every nonzero cap and retained interval lies in 1<|x|<2, so the entire pressure proof, its endpoint identities and finite-before-subtraction argument remain unchanged. The uniform energy bound and origin-centered dilation then give the same contradiction R^(α+β+2-n)∫_(B_1)(fu+gv)→∞. This closes the weak finite-energy extension through the full proof.

The singular examples in section 7 do not invalidate it: for a scaling-power pair, fu and gv have radial integral power r^(n-3-α-β), so local energy diverges whenever α+β≥n-2, including the subcritical range in question. Conversely, merely knowing that the nonlinear sources are integrable and the puncture flux vanishes is insufficient, as those examples demonstrate. Positive point masses are not covered: their fundamental-solution terms change the potential marginals, and local energy integrability alone has not been used to discard them.

This cutoff passage is a standard dominated-convergence extension of the paid source virial. Whether classical local removability already forces origin continuity under these joint assumptions has not been established by a primary-literature comparison here. Accordingly, no new regularity freedom, literature novelty, independent substantial operation, or nominee is asserted on this basis.

## 13. Expanded algebra for the two exact calculations

For T=1+r^κ and s>0,

-d²(T^-s)/dr²-(n-1)r^-1 d(T^-s)/dr
=κs r^(κ-2) T^(-s-2)[(n+κ-2)+(n-2-κs)r^κ].

Substituting s=α/κ and pβ=α+κ gives T^(-s-2)=T^-1·(T^(-β/κ))^p, proving both profile equations in section 6 without numerical approximation.

For the radial Pohozaev calculation, differentiating the first bracket E0=r^n[U'V'+r^B U^(q+1)/(q+1)+r^A V^(p+1)/(p+1)] and substituting the radial equations gives

E0'=(2-n)r^(n-1)U'V' +(n+B)/(q+1) r^(n+B-1)U^(q+1)
 +(n+A)/(p+1) r^(n+A-1)V^(p+1).

The derivatives of r^(n-1)VU' and r^(n-1)UV' are respectively r^(n-1)U'V'-r^(n+A-1)V^(p+1) and r^(n-1)U'V'-r^(n+B-1)U^(q+1). Multiplying by the displayed coefficients in section 9 cancels the two nonlinear terms and leaves precisely γr^(n-1)U'V'. No symbolic-algebra package is required. The available rational arithmetic checks confirm the concrete exponent choices; SymPy was unavailable and was not installed.
