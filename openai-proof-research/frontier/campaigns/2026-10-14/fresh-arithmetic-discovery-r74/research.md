# T047S74: full scope unresolved

This is an author research archive, not a completed candidate, contribution assessment or independent proof verdict. The unchanged target is scope-freeze.md. Its last assertion, nonpolynomiality under arbitrary complex-algebra isomorphisms, remains unproved. The technical deductions below do not replace it.

## 1. Paid global algebra, with the changed coefficients checked

Write f=u^3+t^7 throughout. In P=C[p,s,u,t,F,J] put x=s^2+f+p^2F, y=s+x(x-f), z=sx+p^2J and H as frozen. Direct expansion gives

    xy-z(z+1)=p^2(H+pu).                                      (1)

Over C[p,p^{-1}], the variables (x,y,z,u,t) are coordinates: recover s=y-x(x-f), F=p^{-2}(x-s^2-f), J=p^{-2}(z-sx). Thus H=p^{-2}(xy-z(z+1))-pu is a coordinate after p is inverted, and A[p^{-1}]=C[p,p^{-1},x,y,z,t]. At p=0 write x0=s^2+f. The change

    L=x0^2 F-(1+2s x0)J,
    M=(1-2s x0)F+4s^2 J

has determinant1 and inverse F=4s^2L+(1+2s x0)M, J=-(1-2s x0)L+x0^2M. It makes H mod p the coordinate L. In particular H is not divisible by p. Since its localization is prime, unique factorization in P proves H prime before localization (any extra factor would have to be associated to p). Hence A is integral of dimension5.

The p-invertible open is smooth. At p=0, the F,J partial derivatives of H are x0^2 and -(1+2s x0); their ideal is the unit ideal by the determinant identity. Thus A is smooth globally.

For every prime of C[p], H is a relative coordinate: the generic prime and nonzero closed points use (1), while p=0 uses L. Dutta–Lahiri, arXiv1908.03549v1, Theorem3.4, applies to the one-dimensional affine base C[p] and the five relative variables s,u,t,F,J. It makes H one-stably a coordinate over C[p]. Quotienting by H gives A[w]≅C^{[6]}. This is the actual compatible primary reduction, not an inferred extension of a theorem over C[p,t]. Its Lemma3.3 and Theorem3.4 proofs use the exponential shift and residual-coordinate transfer already credited by source047.

For an explicit check, the source exponential still works: in localized coordinates use Δ=-p^2∂u fixing p,x,y,z,t. Then

    Δs=-3p^2 x u^2, ΔF=(6sx+3)u^2, ΔJ=3x^2u^2,
    Δu=-p^2, Δp=Δt=0, ΔH=p^3.

The source polynomial inverse following L*=pu-p^2Q(0) also works verbatim with x0=s^2+f. These are coefficient substitutions within an already paid operation. No new claim rests on the symbolic checks.

## 2. The full conditional reduction

All six proof sections of source047 were read. The changed coefficient f enters the following identities polynomially; it is not treated as an invariant of an arbitrary action.

Let S=C[p,x,y,z,u,t]/(xy-z(z+1)-p^3u) and R=S/pS. Formula(1) embeds S in A and identifies their p-localizations. The p-order filtration is defined just as in source deg:valuation. Put

    s_R=y-x(x-f), f0=x-s_R^2-f, g0=z-s_R x, I=(f0,g0).

Then the source division-by-p and leading-kernel argument proves, for this changed ring,

    G=gr A=R[τ,I/τ^2],
    G≅C[p,s,u,t,F,J]/(H_top),
    H_top=x^2 F-(1+2sx)J-p^2J^2.

The presentation weights are (-1,0,0,0,2,2). To check the changed-ring interface: after inverting p, the kernel of the initial-form substitution is the prime equation xy-z(z+1); H_top is not divisible by p. Thus its contraction is exactly (H_top). For a representative of excessive maximum weight, subtract H times the homogeneous quotient of its top term by H_top. The replacement decreases the maximum weight by at least1, bounded below by the element's fixed p-valuation degree. This proves that no extra initial generators occur. Smoothness is the same unit-ideal Jacobian test as above. In particular F has degree2 since f0≠0, as witnessed by x=z=0.

Use the determinant ring

    T=C[a,d,b,c,u,t]/(ac-bd-1),
    x=ab, y=dc, z=db,
    v=a^3 b-a^2 f-d^2.

The two Laurent charts D(z+1),D(z) in source prop:principalization remain unchanged with u,t adjoined. They give the same line bundle and faithful flatness. With h=x-f and C1=c^2-b^2h, the global formulas

    f0=C1 v, g0=b^2 v,
    a^2(1-2bd) C1+[d^2(3+2bd)+a^2(1-2bd)h]b^2=1

give I T=(v). Thus the bundle pullback is

    Gtilde=T[τ,V]/(τ^2 V-v).

Its valuation degrees are deg(T)=0, deg τ=-1, deg V=2. Fiber weights are (a,d,b,c,u,t,τ,V)=(1,1,-1,-1,0,0,0,2).

If A were a polynomial fivefold, one of its five polynomial coordinates would have positive filtration degree, since F does. Differentiation in a different coordinate induces a nonzero homogeneous locally nilpotent derivation on G with a positive-degree invariant, using the exact representative argument above. Source prop:linearization is already a general theorem for any smooth integral affine base and any line bundle; its stipulated scope applies to G. The normalization argument in prop:homogeneous-lift retains valuation degree and fiber weight, without asserting preservation of R or T.

The exact homogeneous pieces of Gtilde are τ^{-j}T for j<0, V^l T for j=2l≥0, and τ V^{l+1}T for j=2l+1≥1. The positive-degree invariant is divisible by V; factorial closure of the LND kernel makes V invariant. If τ is fixed, divide the restricted derivation by its τ power to get a nonzero LND E on T of fiber shift0 with E(v)=0. If τ moves, its shift is 2l+1, and the values on T have the factor τ V^{l+1}. Dividing gives a derivation E:T→T of shift -2(l+1). The LND order falls by ν(τ)+1 under each E application, proving local nilpotence. Since ν(v)=2ν(τ), applying E twice would produce order -2; consequently E²(v)=0. This is the source's actual extraction proof, unchanged in its operative hypotheses by adjoining t and replacing f.

Therefore polynomiality of the frozen A would imply

    E≠0, E∈LND_C(T), E homogeneous of fiber shift e≤0, E²(v)=0. (B)

Excluding(B) would finish the target. It has NOT been excluded. The deduction to(B) is an inherited mechanism with the algebraic interfaces checked, not a new substantial conclusion. No truth audit of source operations is made.

## 3. First attempt: retain both leading summands

Give T auxiliary degrees

    (a,d,b,c,u,t)=(0,21,-21,0,14,6).

They preserve ac-bd-1. With N=d²+a²(u³+t⁷), deg N=42 whereas deg(a³b)=-21. The highest auxiliary component E' of an E in(B) is nonzero, locally nilpotent, and retains the same fiber shift. This follows from the finite shift decomposition on the six generators, exactly as in source prop:rigidity. Taking the top component in E²(v)=0 gives

    (E')²(N)=0.                                               (2)

In K=Frac(T), let A(q),D(q),U(q),T0(q) be the exponential orbit polynomials of a,d,u,t. Then

    D(q)²+A(q)²[U(q)³+T0(q)⁷]=N+q E'N.                       (3)

All four polynomials have their original algebraically independent nonzero elements at q=0, subject only to the determinant relation for a,d,b,c. In particular the right side is nonzero. The exponential determinant equation supplies A(q)C(q)-B(q)D(q)=1, hence gcd(A,D)=1 in K[q]. These are available constraints, not a solution of(3).

The original two-term abc step counts roots of a monomial power; it cannot replace deg(U³+T0⁷) by max(3degU,7degT0) without controlling cancellation. For example, the formal polynomials U=u+q^7, T0=t-q^3 have cancellation of degree21 and their sum of powers has degree18. They are NOT asserted to arise from one LND orbit. This only checks why the omitted no-cancellation inference is unavailable.

A valid supporting case is the following. If E'a=E'd=0, then(3) makes U³+T0⁷ a nonzero polynomial of degree≤1. A common zero of U,T0 would have multiplicity≥3 in this sum, impossible. If either is nonconstant, their highest terms must cancel, so 3degU=7degT0=M>1. Mason–Stothers gives M≤degU+degT0=(10/21)M, contradiction. Thus E'u=E't=0. Differentiating the determinant yields E'b=a h, E'c=d h with h=cE'b-bE'c. Localizing at C[a,d,u,t]\{0} gives a locally nilpotent derivation of Q[b], so h∈Q. The a- and d-charts imply T∩Q=C[a,d,u,t], by the coprime-denominator argument. But h has fiber weight e-2<0 and this polynomial ring has no negative weights. Hence h=0, contradicting E'≠0.

This proves that any possible E' from(B) must move at least one of a,d. It does not prove that such motion is impossible. Restricting the frozen target to actions fixing them is forbidden as a repair and is not done here.

Finston–Maubach2010 Theorem2.5/Lemma2.7 were tried at their actual reciprocal-exponent interface. In the four-term identity D²+A²U³+A²T0⁷-L=0, the displayed exact-power exponents can be taken as (2,1,1,1); their reciprocal sum is7/2, exceeding the required1/2. One may instead view A²U³=(AU)²U, but then the remaining U is a moving coefficient; adjoining cube roots of A changes the polynomial/domain and local-nilpotence hypotheses. Even if L were constant, the common A² factor and gcd/subsum conditions must be treated. None of those changes is an application of the read theorem. We do not claim its failure establishes that all refinements of Mason must fail.

## 4. Second attempt: the strongest located root-adjoining reduction

Freudenburg–Moser-Jauslin, author-host version of *Locally nilpotent derivations of rings with roots adjoined*, Lemma4.1, Theorem4.1 and Corollary4.1 give the actual relevant operation. Suppose E' satisfies(2). Adjoin r with r^5=N and define

    D|T=r^4 E',       Dr=(E'N)/5.                             (4)

This is exactly their Lemma4.1 with f=-N. It preserves r^5-N. Local nilpotence follows by induction on the E'-order of each x∈T: E'N is invariant, r has D-order≤1, and Dx=r^4E'x is a product of elements already killed by sufficiently high iterates. This construction is credited in full; it is not a new bridge.

For clarity, B=T[r]/(r^5-N) is a domain. Modulo N the determinant equation makes a invertible: expanding (ac-bd)^2 and substituting d²=-a²f gives an explicit inverse for a. Consequently

    T/(N)≅C[a,a^{-1},b,u,t,z0]/(z0²+u³+t⁷),   z0=d/a.

This is a domain because u³+t⁷ is not a square in C(u,t), for instance by its odd degree valuation at u=∞. Thus(N) is a height-one prime of the smooth ring T, and the local ring at(N) is a DVR with uniformizer N. Eisenstein at N proves r^5-N irreducible over Frac(T); monicity then gives the stated domain embedding.

The derivation(4) is homogeneous for the natural Z/5 grading over T and for the fiber grading that multiplies base weights by5 and assigns r weight2. Its latter shift is8+5e≤8. The primary Corollary4.1 proves an equivalence with this cyclic-homogeneous LND existence; it does not prove its absence. Ordinary rigidity of B is false: a∂b+d∂c fixes N and r and gives a nonzero LND, of rescaled fiber shift10. A successful argument needs to exclude the specified lower-weight cyclic-homogeneous derivations while allowing that positive one.

The same primary Theorem8.1 and Theorem8.2(b) do give stable rigidity of the Brieskorn surface z0²+u³+t⁷=0, since1/2+1/3+1/7=41/42≤1. This identifies a promising exact invariant on the divisor N=0. It does not make D tangent to that divisor: E'N may be nonzero, so E' need not descend to T/(N), and a need not be invariant, so localizing at a need not preserve local nilpotence. Substituting the stably rigid divisor for the whole root ring would omit this compatibility operation. We found no proof that it is automatic.

The follow-up Daigle–Freudenburg–Moser-Jauslin abelian-grading paper was located but its author-host PDF could not be fetched (terminal connection refused; web502). Its abstract/snippets are navigation only and supply no theorem in this report. In particular, no highest component for a finite grading is assumed.

## 5. Remaining scope and comparisons

The precise missing sufficient step is to exclude(B), or to supply another global obstruction to arbitrary polynomiality of A. The strongest reduced necessary condition obtained is(2) for a nonpositive-fiber-shift LND moving a or d, with the actual orbit identity(3) and the determinant coprimality retained. The root-adjoining route translates this to a cyclic-homogeneous weighted rigidity problem; it does not solve it.

No counterexample to the frozen theorem, no proof of its last clause, and no eligible full candidate emerged. Smoothness, integrality, stabilization, conditional extraction, fixed-coordinate exclusion, the formal leading cancellation example, and the root-ring reduction are not substitute nominations. No local, fixed-parameter, equivariant, finite-degree or generic variant is promoted. There is no formalization or manuscript/release work.

Integrated paid/unpaid comparison: Dutta–Lahiri pays one-stable coordinates; source047 pays exponential formulas, the exact filtered modification, line-bundle lifting and degree/sign extraction; Mason and Finston–Maubach pay the constant-coefficient/monomial rigidity steps; Freudenburg–Moser-Jauslin pays root adjoining and the stable rigidity of the divisor. What remains unproved is compatibility of unrestricted determinant-coordinate motion with the two-variable sum. Merely writing a longer version of the paid operations, or choosing exponents to satisfy a familiar compiler, would not supply it. This is a bounded source/primary comparison, not worldwide priority clearance or a contribution rating.
