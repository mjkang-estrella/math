# Source divisors, integral triangular inversion, and their exact fixed-fiber threshold

PREFREEZE feasibility derivations. No author theorem or mathematical grade is assigned. Source060 and its operative proofs are held true. The purpose is to determine what a proposed quantitative family operation would still have to do after the strongest actual payment.

## Integral identification, including orientation and framings

Let X satisfy Source060's full main hypotheses. For its analytical compact-data construction first retain its actual no-effective-square-zero branch. Its proved shell and topology identify its cyclic cover Y with the Kato universal cover of DT Section 4. This identification is made after, not as an input to, the source curve-production proof.

By compact-support Poincaré duality a source relative class e corresponds to a finite integral homology combination v=sum x_j u_j. The source equality e²=K.e gives

    sum_j x_j(x_j-1)=0.

Each summand is a nonnegative integer, so x_j is 0 or 1 for every j. Since e²<0, the set S={j:x_j=1} is finite and nonempty, with |S|=-e². This uses the actual compact class with end framings. It is not a decomposition inferred solely from a class downstairs or from rational coefficients. The diagonal compact intersection pairing also makes Hc²(Y,Z)->H²(Y,Z) injective here: a nonzero finite vector has nonzero evaluation against some compact u_j. Thus its ordinary class retains this finite vector in the present cover.

The source zero divisor D is effective, locally finite and one-end bounded, and its components are all compact rational. DT's list of compact rational lifts is (C_j). A primitive height and the elementary Kato-chain height differ, up to a sign and scaling by b, by a bounded periodic function. Hence source one-end boundedness says the support indices of D are bounded below or bounded above. No sign is assumed from the two papers' conventions.

Write D=sum_j d_j C_j, d_j>=0. Compact testing of its Borel–Moore class yields the pointwise finite relation

    x_j = d_j - sum_{1<=r<=b+1, r<=s_{j-r}} d_{j-r}.       (1)

Only b+1 earlier indices occur; no pairing of two infinite cycles is used. If the d_j were bounded above in index, let J be their largest nonzero index. At J+1 the right side is at most -d_J<0, since s_J>=1. That contradicts x_{J+1}>=0. Thus D is bounded below in the DT index. This pays the end-orientation compatibility: f=T^{-1} with the source height normalization. Its support escapes to the pseudoconcave/source-negative end.

For sequences bounded below, (1) has a unique solution, found successively from the lowest possible index. If x is one impulse at i, this is exactly DT's fundamental series E_i. Linearity therefore proves the precise identity

    D = sum_{i in S} E_i.                                  (2)

Consequently the source auxiliary operator and its freely prescribed correction rate do not change the effective divisor for this fixed relative class. This does NOT assert that the induced holomorphic isomorphism of line bundles preserves both prescribed smooth end frames. The unframed section/bundle pair is O(D) with its canonical section; a stronger framed gauge statement is not inferred.

This is a composition with DT's already proved uniqueness and recursion, not a new classification or shell theorem. On the Enoki branch the source does not construct these weighted data; DT constructs E_i directly after the paid Enoki shell criterion. A statement about E_i for all minimal positive-b2 surfaces uses that separate branch, not invalid acyclicity across square-zero divisors.

## Periodic recurrence and a finite matrix

Fix i=0 by an index translation, put L=b+1, and write a_j=coefficient of C_j in E_0, with a_0=1 and a_j=0 for j<0. DT's exact recurrence is

    a_j = sum_{d=1}^L c_{j,d} a_{j-d},
    c_{j,d}=1 if d<=s_{j-d}, and 0 otherwise,  j>=1.          (3)

The coefficients are b-periodic in j. In particular c_{j,1}=1. Define the L-component state v_j=(a_j,a_{j-1},...,a_{j-L+1})^t and the nonnegative integer companion matrix M_j with first row (c_{j,1},...,c_{j,L}) and ones immediately below the diagonal. Then v_j=M_j v_{j-1}. With

    A=M_b ... M_1,  B_0=I,  B_r=M_r ... M_1 (1<=r<b),

we have v_{mb+r}=B_r A^m v_0. Every residue-class generating function is therefore the exact rational function

    F_r(z)=sum_{m>=0} a_{mb+r} z^m
          = row_1 B_r (I-z A)^(-1) v_0.                    (4)

This is a formal power-series identity; it already holds before choosing a convergence radius. Each denominator divides det(I-z A). Cancellations are allowed, so one must not declare every determinant zero to be a pole of every F_r. Integer recurrence, Cayley–Hamilton, and phase products suffice; an irreducibility assumption on A is unnecessary.

Let rho be the spectral radius of A. For sufficiently large m all coordinates of A^m v_0 are positive, because a_j>=1 for every j>=0. Hence the positive state sees every nonnegative block. A nonnegative left Perron vector gives a lower bound on the sum of the next L coefficients by a positive constant times rho^m. The finite-dimensional resolvent or Jordan form gives an upper bound C_eta(rho+eta)^m for each eta>0. A phase block of b consecutive coefficients is comparable, up to a fixed finite shift and constant, with an L-state since a_j is nondecreasing. Thus the aggregate sequence of period coefficients has exact exponential rate rho, and at z=1/rho its nonnegative series diverges. This argument does not assume a simple Perron eigenvalue or invent a spectral gap.

There are at most (b+1)^b possible periodic integer words (s_0,...,s_{b-1}) obeying the displayed bounds; some are not geometric words. Using this larger finite set only supplies an upper bound and asserts no realizability. For an impulse, induction in (3) gives a_j<=2^j: indeed sum_{d>=1}2^{j-d}<2^j. Thus rho<=2^b. The sharper scalar majorant is the root theta_L in (1,2) of sum_{d=1}^L theta_L^(-d)=1, giving a_j<=theta_L^j and rho<=theta_L^b. These are elementary bounds from the paid recurrence, not nominees.

If all s_j=1, then every a_j=1 and rho=1. Otherwise some s_r>=2, repeated every b steps. For every j>=0, an r in [j,j+b-1] with s_r>=2 gives a_{r+2}>=a_{r+1}+a_r>=2a_j; monotonicity yields a_{j+b+1}>=2a_j. Therefore rho>=2^(b/(b+1))>1. This lower bound is deliberately coarse and valid also for b=1. Exact sample matrices and coefficients are retained in calculation-values.json. The familiar Fibonacci, powers-of-two and 1+sqrt(2) examples are already in DT.

## Exact weighted area, with the actual geometric factor retained

Choose a lifted Hermitian metric omega and a smooth height h with h(fy)=h(y)-1. For beta real define the extended nonnegative weighted mass

    W_beta(E_0)=integral_{E_0} exp(beta h) omega.

For the b compact reference curves C_0,...,C_{b-1}, put

    V_r(beta)=integral_{C_r} exp(beta h) omega > 0.

Their finiteness is a fixed-fiber statement. Deck invariance of omega and the height increment give

    integral_{C_{mb+r}} exp(beta h) omega
        = exp(-beta m) V_r(beta).

Tonelli for nonnegative integration yields the exact identity, including possible infinity,

    W_beta(E_0)=sum_{r=0}^{b-1} V_r(beta) F_r(exp(-beta)).   (5)

It follows from (4) and the positive-state argument that

    W_beta(E_0)<infinity iff beta>log(rho).                  (6)

At equality the positive period sum diverges; below equality exponential growth forces divergence. Finite sums of E_i have the maximum threshold of their nonzero summands; for a single periodic word changing the initial phase gives the same nonzero spectral radius (cyclic products have the same nonzero spectrum), so all E_i have this same threshold. A deck shift only multiplies W_beta by exp(-beta times the shift). No metric-free prefactor is asserted. Formula (5), not just the rational generating function, is the exact interface needed in a family.

Nothing here strengthens the shell embedding or its uniqueness. These calculations concretely identify the paid discrete part and the geometric factor that cannot be discarded in the relative question.
