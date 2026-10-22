# r192 — higher relation calculations, PREFREEZE

No theorem has been frozen. These are retained derivations and compatibility calculations, not an author-proof nominee. All operative Source316 proofs at the pinned revision are stipulated true. The source and the primary proof passages recorded in INTERFACES preceded this extended document. Sum and Hưng were read after the short RESEARCH-NOTES entry; the complementary history search was also late relative to that entry. No frozen claim changed.

## 1. The operation investigated

The specific direction is a higher relation-level extension of the source's suspension-ideal obstruction. Write A for the binary Steenrod algebra, E=Λ(q_0,q_1,...) for its exterior sub-Hopf algebra, B=A/(E^+A), and

    M_n = Σ^n d_0^n D_k,   D_k=F_2[d_0,...,d_(k-1)].

Here k>=1, n>=0 and |d_j|=2^k-2^j. The source identifies B with a doubled-degree copy of A and proves injectivity of the Tor_1 edge in even internal degree when n≡k mod 2. The prospective operation was a uniform description of the NEXT edge kernel

    K_(k,n,t) = ker[Tor_2^A(F_2,M_n)_t
                    -> Tor_2^B(F_2,H_0(E,M_n))_t],          (1)

for every k,n with n≡k mod 2 and every even t, retaining the maps induced by inclusions d_0^(n+1)D_k -> d_0^nD_k after the necessary suspension shifts. A description must determine actual relations uniformly, rather than rename (1) or supply independent finite Gaussian eliminations. The intended use is to understand whether the source's exponent-floor operation has a coherent next relation level. No claim that this would realize new spherical classes, compute stable stems, or prove an algebraic Curtis conjecture is made.

What follows constructs the full exterior part, an explicit Laurent contraction, exact floor residuals, a reduction of (1) to its first transgression, and a nonzero transgression with a parameterized chain identity. It does not give a full-scope presentation of (1).

## 2. Exact localized coordinates and contraction

Put x=d_0, y_j=d_j for 1<=j<k, L=D_k[x^-1], and

    R=F_2[x^2,x^-2,y_1^2,...,y_(k-1)^2].

For the first k primitives, the source proves

    q_i=x ∂/∂y_(i+1)                (0<=i<k-1),
    q_(k-1)=x(x∂/∂x+Σ y_j∂/∂y_j).

Their action is R-linear. Let v=x^-k y_1...y_(k-1). For S a subset of {0,...,k-2}, and ε in {0,1}, set T=S union ({k-1} if ε=1). Direct differentiation gives

    q_T v=x^(-k+|S|+ε) ∏_(j-1 notin S) y_j.                (2)

There are 2^k such monomials. For each parity pattern of the y exponents, S is fixed; ε supplies the two parities of the x exponent. Thus they are an R-basis of L, not just a spanning family after passing to a fraction field. In particular L is free over E_[k]=Λ(q_0,...,q_(k-1)) with coefficient space R and generator v. This makes the projectivity operation in the source completely explicit; it is credited to that operation, not offered as a new finding.

Use the tensor product of the periodic resolutions of the k exterior generators. A basis element in homological degree s is

    [a_0,...,a_(k-1)] ⊗ f,    Σa_i=s,
    d([a]⊗f)=Σ_(a_i>0)[a-e_i]⊗q_i f.                     (3)

There is NO factor a_i in (3). The resolution basis is a divided-power basis. Replacing (3) by ordinary polynomial differentiation would wrongly kill repeated generators in even resolution degree.

For one exterior generator, on coefficients 1,q define h([a]⊗q)=[a+1]⊗1 and h([a]⊗1)=0. The identity dh+hd=1-ip holds, where p retains only [0]⊗1. Tensor these contractions, in order q_0,...,q_(k-1):

    H=h_0⊗1+ i_0p_0⊗h_1⊗1+ ... .                        (4)

Via (2), this is a fully specified operator on Laurent monomials. For f=x^c∏y_j^b_j, put T_i=1-(b_(i+1) mod 2) for i<k-1 and

    T_(k-1)=(c+k-Σ_(i<k-1)T_i) mod 2.

Find the first i with a_i>0 or T_i=1. If none exists, H=0. If that first index has T_i=0, H=0. Otherwise increase a_i by one, replace x^c by x^(c-1), and, when i<k-1, increase b_(i+1) by one. All remaining exponents stay fixed. This is (4), with the square coefficient in R held fixed. Every nonzero H-term lowers the x exponent by EXACTLY one.

For every positive-homological-degree chain, dH+Hd=1. At homological degree zero the residual projection retains precisely the R multiples of v, corresponding to the above-floor parity pattern c≡k, every b_j odd. The displayed tensor contraction proves the identity in every degree and rank. The independent finite check in private/exterior_calculation.py covers 10,071 Laurent monomial basis cases, k=1,...,4 and homological degrees 1,...,3, including negative x exponents. It checks d^2=0, the contraction identity and the exact exponent loss; these finite calculations are not the proof of the general formula.

## 3. The exact floor contribution

Ignore the shift temporarily and set J_n=x^nD_k. In (3) each nonzero differential raises the x exponent by exactly one. A chain splits as a finite sum by exact x exponent; different pieces have different differential exponents. Hence a cycle splits into cycles at each exponent.

For s>0, every cycle supported at exponents c>=n+1 is the boundary of its H image, which is already in J_n. Conversely no boundary in J_n has a term at exponent n. It follows that

    Tor_s^{E_[k]}(F_2,J_n)
       = {cycles in (3) all of whose coefficients have exponent n},  s>0.   (5)

Equation (5) is a canonical identification via taking the floor component, not a choice of homology basis. There are no boundaries to quotient out on its right side.

The kernel in (5) is concrete. Write f_a=x^n F_a(y). Its equation, at each multi-index a of size s-1, is

    Σ_(i<k-1) ∂F_(a+e_i)/∂y_(i+1)
       +(n+Σ y_j∂/∂y_j)F_(a+e_(k-1))=0.                (6)

Each specified internal degree gives a finite polynomial matrix. This is a floor kernel, not a statement that every floor monomial is a cycle. For k=1, for instance, n odd gives no positive Tor for E_[1]; n even gives the one-dimensional floor class [s]⊗x^n in every s>0. The latter fact follows directly from q_0x^c=cx^(c+1).

Restore Σ^n. At the floor, coefficient degree has parity n+n=0; every resolution generator q_i has odd degree. Thus

    Tor_s^{E_[k]}(F_2,M_n)_t=0 if t not≡s mod 2, s>0.   (7)

For s=0, the source coinvariant calculation gives the floor monomials plus above-floor monomials c≡k and all b_j odd. Their degrees have parity 0 and n+k respectively. When n≡k, H_0(E_[k],M_n) is entirely even.

The inclusion J_(n+1)->J_n kills (5) for s>0: its cycles become above-floor cycles and the SAME H fills them. This supplies a simultaneous filling for these exterior cycles, rather than unrelated existence choices at different floors. It says nothing yet about the full A-resolution.

## 4. All Milnor primitives, without mistaking action identities for algebra identities

The source root-polynomial recurrence, also compared with Sum's determinant calculation, gives for each l>=k

    q_l = Σ_(i<k) a_(l,i)^2 q_i                              (8)

as operators on D_k, with a_(l,i) in D_k. The coefficients are obtained recursively from

    q_(k+t)=Σ_(j<k)d_j^(2^(t+1))q_(j+t).

Crucially (8) is an operator identity on this module, not an equality of elements of the Steenrod algebra. It also holds on every J_n and on L. Coefficients are squares, so the q_i commute with multiplication by them.

Here is a legitimate chain change implementing (8). Use R_0=D_k^2, without localizing x. Extend the exterior algebra to R_0, and for a finite tail k<=l<=N change generators to

    q'_l=q_l+Σ_(i<k)a_(l,i)^2q_i,   q'_i=q_i (i<k).         (9)

This is an invertible triangular, augmentation-preserving automorphism of the exterior R_0-algebra. It preserves degrees; all generators remain square-zero. On J_n, q'_l acts as zero. The corresponding divided-power resolution change is

    e'_l=e_l+Σ a_(l,i)^2e_i,

extended by divided powers. For example

    γ_2(e_l+a^2e_i)=γ_2(e_l)+a^2 e_l e_i+a^4γ_2(e_i),       (10)

so the middle term must be retained. Naturality of the divided-power Koszul resolution makes this a chain isomorphism, not only an equality on degree-one chains. Extending scalars does not change the original complex: Γ_(R_0)⊗_(R_0)J_n=Γ_(F_2)⊗J_n.

Consequently, as graded vector spaces/R_0-modules, with an explicit resolution splitting,

    Tor_s^E(F_2,M_n)
      ≅ ⊕_(q+p=s) Tor_q^{E_[k]}(F_2,M_n) ⊗ Γ^p(e'_k,e'_(k+1),...).  (11)

The tensor factor in (11) denotes copies shifted by the original degrees |q_l|. Finite tails suffice in each internal degree, because M_n is bounded below and |q_l| tends to infinity. The same coefficients (8) work for every ideal inclusion, so (11) respects those inclusions, after adjusting the suspension shift.

Equation (11) is NOT a B-module splitting. It is a change over the square coefficient ring that commutes with the exterior action. Squares are annihilated by Milnor primitives but not by all Steenrod squares. This distinction is the remaining compatibility issue, rather than a failure to construct the exterior change of basis.

Combining (7), the source H_0 description, and the odd degrees of the tail generators proves, when n≡k,

    Tor_s^E(F_2,M_n)_t=0 unless t≡s mod 2, for every s>=0. (12)

This is retained as an elementary extension of the paid exterior operations. It is not submitted for a mathematical grade or offered in place of the full operation (1).

## 5. The full Steenrod comparison and the first unpaid map

For the normal sub-Hopf algebra E and quotient B, the standard change-of-rings double resolution has homological spectral sequence

    E^2_(p,q,t)=Tor_p^B(F_2,Tor_q^E(F_2,M_n))_t
        => Tor_(p+q)^A(F_2,M_n)_t,
    d_r:(p,q,t)->(p-r,q+r-1,t).                           (13)

It can be formed in finite internal degree and then passed to the directed union; no infinite completion is required. B is in even internal degrees. By (12), row q in (13) is in internal parity q. Every even-r differential changes that parity and is zero. Odd-r differentials, starting with d_3, are not excluded.

For s=1 and even t, only row zero contributes; no differential can enter or leave position (1,0). This recovers the source's even-degree edge injection, indeed the corresponding edge is an isomorphism at this internal parity. This observation is source/classical payment, not a candidate.

For s=2 and even t, there are TWO possible pieces, (2,0) and (0,2). The first survives. The only possible incoming differential to (0,2) is d_3 from (3,0), and no differential leaves (0,2). Thus the exact new kernel is

    K_(k,n,t) ≅ coker[
       d_3:Tor_3^B(F_2,H_0(E,M_n))_t
              -> H_0(B,Tor_2^E(F_2,M_n))_t].             (14)

The identification includes the filtration injection of this cokernel into Tor_2^A. Equation (14) is a reduction, not a solution by assigning a name to the cokernel. Sections 2–4 compute its exterior input concretely, and Section 6 computes a genuinely nonzero d_3, not merely its possible bidegree.

## 6. A complete first transgression, with a parameterized chain filling

Take k=n=1, write x=d_0, and M=Σ xF_2[x]. The first primitive acts freely in pairs x^(2a+1)->x^(2a+2), so Tor_q^{E_[1]}(F_2,M)=0 for q>0 and H_0 has representatives Σx^(2a+1). The doubled-degree quotient acts by

    Sq^(2r)[Σx^(2a+1)]=binom(a,r)[Σx^(2(a+r)+1)].         (15)

After halving degrees this is ΣF_2[x]. In degree 8, Tor_2^E is one-dimensional, with generator represented by the second divided power of e'_1=e_1+x^2e_0 on Σx. All other tail or coefficient possibilities have greater degree. There is no lower-degree Tor_2^E class on which a positive B operation could act. Hence E^2_(0,2,8)=F_2.

In the normalized A-bar complex, omit Σ from coefficients and put q_0=Sq^1 and q_1=Sq^2 Sq^1+Sq^3. The generator is

    Z(c)=[q_1|q_1]x^c
          +([q_0|q_1]+[q_1|q_0])x^(c+2)
          +[q_0|q_0]x^(c+4),                            (16)

initially c=1. This follows from (10) and the shuffle comparison for two distinct exterior generators. All bars in (16) have total internal degree c+7, including the suspension. Since q_1=x^2q_0 on F_2[x], (16) is a cycle for every odd positive c.

Put a=Sq^1, b=Sq^2 and retain q=q_1=a b+b a. Define a sum of seven written terms (nine after expanding q):

    W(c)=([a|a|b]+[a|b|a]+[b|a|a])x^(c+2)
          +([a|b|q]+[a|b a|b]+[b|a|q]+[b|b|b])x^c.    (17)

All coefficients satisfy the original ideal floor. A direct use of the bar differential gives

    dW(c)=Z(c)+ε(c){[a|a]x^(c+4)
                       +[a|b a]x^(c+2)+[b|b]x^(c+2)},  (18)
    ε(c)=binom(c,2) mod 2,       c positive odd.

To verify this for all c, use d[u|v|w]z=[uv|w]z+[u|vw]z+[u|v](wz), the relations a²=0, ab=Sq³, b²=aba, and Sq^r x^c=binom(c,r)x^(c+r). For odd c, binom(c,2)=binom(c,3)=ε(c), while binom(c+2,2)=1+ε(c). The merged-bar terms are independent of c. Expanding q in (17) and applying these three coefficient identities leaves exactly the three residual terms in (18). This proves (18), rather than extrapolating from finitely many samples.

For c≡1 mod4 the residual is zero, so (17) is an explicit filling of (16). For c≡3 mod4 it is NOT a filling; its precise residual must be retained. In particular dW(1)=Z(1), so the generator of E^2_(0,2,8) dies in full A-homology.

On the other side, E^2_(3,0,8) is Tor_3^A(F_2,ΣF_2[x])_4 after halving, and is one-dimensional: [Sq¹|Sq¹|Sq¹]⊗Σ1 is a cycle, and there is no degree-four-chain in internal degree four because the minimum is five. There is no d_2 by parity and no other possible incoming differential to (0,2). Therefore

    d_3:E^3_(3,0,8) -> E^3_(0,2,8)

is nonzero (an isomorphism between these two one-dimensional spaces). This is an actual transferred relation, not an assertion inferred only from the location of a possible arrow.

The retained finite bar calculation independently constructs A using admissible words and Adem reduction, acts by binomial coefficients, checks d²=0, and solves the relevant linear equation. It produced the expanded nine-term (17). It also gives C_1,C_2,C_3 dimensions 11,28,32 and differential ranks 0,10,18 at (M,t=8), so Tor_2^A(M)_8=0. The rank statement is supplemental; the explicit filling and degree argument above identify this particular d_3 without treating a numerical table as a general theorem. Calculations for 1<=t<=12 and the c=1,3,...,15 residual checks are retained privately. No stable-stem computation is claimed.

## 7. Why the construction does not yet close the full operation

The exterior operation is fully constructed: all ranks, all floors, exact exponent-one contraction, later-primitive resolution change, and parity. There are genuine higher classes, and the first Steenrod transgression acts nontrivially on them. To determine (1) for all k,n,t one still needs the quotient B action on the floor/tail presentation (11) and an explicit all-rank description of d_3 in (14), compatible with the actual ideal inclusions. Formula (18) is a first relation and exhibits the additional residual when c≡3 mod4. It is not an all-rank, all-degree formula for the entire cokernel. Further odd differentials matter if one asks for higher homological degrees, but they are not smuggled into the stated degree-two task.

The source's Cartier map on H_0(E,-) does not provide this action on higher Tor. Its tensor halving starts from a cycle in I⊗_A M and an independently lifted annihilated functional. At higher degree, these hypotheses do not identify a relation between relations or its homotopy. Our rank-one d_3 shows precisely why simply reusing the degree-one injectivity as a collapse statement fails.

The strongest topological composition is already paid. Kuhn supplies compatible maps from Adams stages to derived ideal powers; Kuhn–Pereira supplies the composition (J^a)^b->J^(ab), with the actual bar-resolution and coefficient-change compatibilities. The source's positive-weight truncation then annihilates every ideal power beyond the cutoff. Applying this at cutoff seven already supplies the filtration-two bound in the Kervaire case. Repeating it at a variable cutoff gives only the known exponential lower-weight rule. It supplies neither the missing B action/d_3 in (14), nor a mapping cone realizing an arbitrary algebraic functional.

Hunter's strongest read journal construction computes a width filtration with quotients D_k/(perfect squares), desuspended and resolved in the unstable category. Its actual tower detector retains Sq¹ and one degree-dependent higher square, and has nontrivial towers. Neither this quotient nor its unstable Ext is M_n or the stable Tor in (13). We have not constructed a chain comparison that would turn its computed towers into the missing map (14). Equating the two because both use Dickson algebras would discard both the ideal floor and the instability condition.

Hưng's single-primitive Margolis calculation contains critical classes and relations among them; Sum computes the later primitive action explicitly. These are stronger payments than an informal appeal to parity. They justify retaining syzygies rather than pretending all cycles are independent monomials. Our exterior calculation uses the stipulated source's full square-coefficient recurrence and periodic resolutions, not a novel Margolis theorem. The actual primary-access limits are in private/READING-LIMITS.md.

## 8. Endpoint

PREFREEZE / no nominee. No exact full-scope new theorem was frozen and no author proof is submitted. The remaining operation is the all-rank, all-floor, all-even-degree relation-level computation in (14), with its B action and ideal-inclusion compatibility. It has been reduced to an identifiable map and carried through a nonzero example with an explicit general c-residual formula. A finite linear-algebra algorithm, exterior-only result, paid Hurewicz theorem, unchanged old target or conditional realization statement is not substituted for it. No exhaustion or general impossibility is claimed.
