# Arithmetic r76: pre-freeze research record

No campaign theorem was frozen or nominated. No independent gate or count is assigned here. The parent supplied campaign status 18/20, separate from the historical baseline. All pinned OpenAI statements and operative proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. This record concerns contract interpretation and new feasibility deductions, not upstream truth.

The three newly read source families were 018 (normal subgroups and simultaneous norms), 066 (complements and Cartier sections), and 201 (algebraic division rings). Historical screens of 037, 199, 202, 210, 247 and 310 were used to avoid developed routes, not counted as new proof-body investigations. After the first screens, work continued into an actual two-norm tensor-lattice calculation and into the matrix/central-parameter interface of the division-ring lifting. Neither yielded a candidate with an identified unpaid operation and a complete credible proof route. No famous general conjecture was frozen to fill the slot.

## 018: the ordinary consequences are already in the source

Both number-field and function-field introductions have `thm:main`: a noncentral abstract normal subgroup is the inverse image of an open normal subgroup of the finite product of anisotropic nonarchimedean local groups. The function-field introduction already states continuity of every finite quotient for this topology. The number-field introduction explicitly gives `cor:positive-density-csp`. Arithmetic r5 had already excluded finite-index and positive-density reformulations. None is reopened here.

The more concrete operation is in function-field `04-norm-tori.tex`, read in full, and number-field `foundations.tex`, lines 599–850. The source does not merely assert an arithmetic conclusion. It identifies the character lattice

    (Z^m / Z(1,...,1)) tensor sign(C2)

for a degree-m symmetric extension and an independent quadratic extension. It reduces the arithmetic obstruction to the cyclic restriction kernel in H², uses a central sign element to produce a mod-2 H¹ class, and splits the resulting extension by Coxeter relations. Its exceptional m=4 proof retains an integral anti-invariant lift to rule out noncommuting disjoint transposition lifts. All of that operation is paid. Relevant labels are `tor:norm-approximation`, `tor:cyclic-detection`, `tor:sign-element`, `tor:symmetric-lattice`, and the number-field `lem:norm-torus` and `lem:foundations-sign-extension`.

### Extended feasibility calculation: two independent symmetric extensions

This calculation was made before any freeze, to determine whether replacing the quadratic factor leaves an unpaid compatibility operation. It is not a nominated theorem.

Let F/k and L/k have degrees m,n≥3, with joint normal closure of Galois group S_m×S_n acting independently on their embeddings. For E=FL consider prescribing both N_(E/F)(a)=h and N_(E/L)(a)=d, subject to N_(F/k)(h)=N_(L/k)(d). The geometric kernel has dimension (m−1)(n−1). With J_r=Z^r/Z1 its character lattice is

    M=J_m tensor_Z J_n.

Indeed, over a splitting field the variables form an m by n array. The relations in the character lattice are the row sums and column sums, with one dependence. Quotienting first by the row relations and then the column relations gives the displayed free lattice. Geometric solvability of compatible nonzero row/column products follows by choosing the upper-left (m−1) by (n−1) entries, then solving the last column and row. Thus this really is the simultaneous-norm torus, rather than the torus for a product of two separate norms.

The strongest compatible reduction in this case is ordinary group cohomology, and it pays the entire calculation:

1. H⁰(S_m,J_m)=0. Apply invariants to 0→Z→Z^m→J_m→0: the first map on invariants is an isomorphism and H¹(S_m,Z)=0.
2. H¹(S_m,J_m)=0 for m≥3. By Shapiro and the same exact sequence this is the kernel of H²(S_m,Z)→H²(S_(m−1),Z). For a finite group H, H²(H,Z)=Hom(H,Q/Z), from 0→Z→Q→Q/Z→0 and averaging. Restriction of the sign character is an isomorphism between the two character groups, including S_3→S_2.
3. For every abelian group A and n≥3, (A tensor J_n)^(S_n)=0. Represent an invariant by a vector in A^n modulo diagonal vectors. A transposition fixes a third coordinate, so its difference from the original vector, if diagonal, must be zero. Invariance under all transpositions then forces every coordinate equal. This argument requires no division by n and works for torsion A.
4. Apply the Hochschild–Serre spectral sequence to S_m normal in S_m×S_n. Since J_n is free, H^q(S_m,M)=H^q(S_m,J_m) tensor J_n, equivariantly for S_n. In total degree two the q=0 and q=1 rows vanish by steps 1–2, and the only remaining term is

       E₂^(0,2)=(H²(S_m,J_m) tensor J_n)^(S_n)=0

   by step 3. Consequently H²(S_m×S_n,M)=0. No calculation of a symmetric-group Schur multiplier and no exceptional-degree repair is necessary.

The source's already general cyclic-detection/duality lemma now supplies the Hasse-principle and weak-approximation transfer over global fields. The finite lattice computation has no parameter losses or missing small-degree cases within m,n≥3. It does not assert stable rationality. The source already handles one factor of degree two when the other has degree at least three; assembling the two ranges is not proposed as another result.

This assessment is based on an actual compatible proof, not on an inference that any short proof is insubstantial. The required integrated operation—simultaneous row/column constraints followed by vanishing of the arithmetic obstruction—factors through the existing double-norm kernel and the standard spectral sequence with its actual hypotheses satisfied. There is no residual matching step here to present to the parent as a new contribution. No worldwide-duplicate claim is made.

### Primary comparison and the degree distinction

Bayer-Fluckiger–Lee–Parimala, *Hasse principles for multinorm equations*, retained October 20, 2018 version, §2, already constructs exactly the simultaneous-norm kernel S_(K,K′) in

    1→S_(K,K′)→Res_(K tensor K′/k) G_m→T_(K×K′/k)→1.

Its Lemma 3.1 identifies Sha¹ of the multinorm torus with Sha² of this kernel torus. This is not the Sha¹ of the kernel needed for its torsors. Therefore their multinorm Hasse principle alone must not be cited as the desired simultaneous-norm theorem. The above lattice calculation supplies the relevant degree-two *character-lattice* vanishing by an already standard compatible route. URL: https://www.math.uni-bielefeld.de/LAG/man/596.pdf .

Demarche–Wei, arXiv:1212.5889v1, Theorem 1 and its complete proof, use permutation restrictions and an injective restriction map for a *product* of norms with independent Galois closure. The equation and lattice differ from the two-prescribed-norm problem; its theorem is not blindly transferred. URL: https://arxiv.org/pdf/1212.5889v1 .

Florence–Hoshi–Yamasaki, arXiv:2605.17427v1, Propositions 5.5–5.6 and Theorem 6.12 with proofs, explicitly supply the tensor-extension sequences and coprime extension-order splitting. Theorem 6.15 then treats stable/retract rationality with coprime permutation orders. These conditions were checked, rather than assuming that arbitrary tensor products preserve rationality. Their Theorem 5.8 is about augmentation *ideals*, whereas the simultaneous-norm character lattice above uses augmentation *quotients*. No duality substitution is hidden. URL: https://arxiv.org/pdf/2605.17427v1 .

Hochschild–Serre, *Cohomology of group extensions* (1953), Chapter II §4 Theorem 2, is the primary spectral-sequence interface used in step 4. Selected original construction and E₂ identification were read; the entire paper was not re-proved. Successful original-paper copy: https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hochschild-serre.pdf .

Correlated discriminants and arbitrary subdirect Galois groups were considered only as navigation. They do not retain the direct-product argument automatically. No all-subdirect theorem, finite obstruction table, or correlated-field candidate was frozen or proved. A failed optional SymPy probe returned ModuleNotFoundError before producing a calculation; it is not evidence for any cohomology claim.

## 066: exact discrepancy retention is the unprovided part

The two source companions were checked separately. The bounded-complement introduction gives `thm:main`, index N(d,epsilon), and the finite-rational-coefficient corollary. Its `reduction.tex` already supplies `lem:threshold-to-complement` and `lem:field-descent`, including general members of a resolved fractional ideal and control of the entire relevant fibre. The Cartier-section companion `thm:main` retains all algebraically closed characteristic-zero fields, and `cor:real-boundaries` already retains real boundaries over C. `lem:H-field-reduction` explicitly handles the point-ideal threshold, general Cartier members, and field extension. These are not new field/denominator/general-member operations.

Chen, arXiv:2403.01154v4, Theorem 1.6, gives the full equivalence between the local threshold and complement formulations. Propositions 3.2–3.3 and their proofs already handle the generalized-pair reduction and the whole-fibre pullback. I read those proofs, not just the abstract. URL: https://arxiv.org/pdf/2403.01154v4 .

One tempting strengthening is not an unpaid operation: a klt n-complement has log discrepancies in (1/n)Z, since n(K_X+Lambda) is Cartier and its pullback is Cartier on every smooth model. Positivity consequently gives 1/n-lc. This supplies a possibly much smaller uniform positive gap, with exactly the dependence of n. It does not retain the original epsilon. Chen Remark 1.2(1) explicitly distinguishes the epsilon-lc complement question, and the source introduction says it does not assert that stronger requirement.

The attempted convex interpolation cannot repair this discrepancy. Given an epsilon-lc real complement Lambda_real and a klt bounded-index complement Lambda_n, their convex combination has a discrepancy lower bound theta*epsilon+(1−theta)/n. If 1/n<epsilon, this reaches epsilon only at theta=1. The endpoint loses the bounded rational index; replacing it with a nearby rational coefficient has not solved that. This is a limitation of that interpolation argument, not a counterexample to epsilon-lc complements. No epsilon-preserving full target was frozen, and the weaker 1/n consequence is not a surrogate nominee.

## 201: scalar lifting is not matrix-preserving lifting

The full `thm:lifting`, `application.tex`, and `division-realization.tex` were read. The source already preserves all old polynomial identities, generation and both transverse directions, produces a new scalar algebraic relation, schedules every polynomial over every countable coefficient stage, and passes from the auxiliary coefficient field to the actual centre. Its finite-stage algebras are not an embedding tower. Their centres may acquire transcendental elements. None of these operations is a new candidate here.

Deo–Bien–Hai, arXiv:1510.08711v2, Theorem 5 and its proof, already gives the finite multiplication-table descent underlying the locally finite/weakly locally finite distinction. The source explicitly credits it. Its subsequent matrix discussion concerns finite generation of GL_n(D), not algebraicity of every matrix. That wording was checked in the actual text. URL: https://arxiv.org/pdf/1510.08711v2 .

I28's original involution argument was located and read before considering this different interface. The opposite-ring tensor zero divisors, degree-11 obstruction, exponent condition, and modified graph are old work. No involution or opposite-tensor repair is proposed here.

The additional feasibility question was whether the scalar construction could preserve algebraicity of every finite matrix over the resulting division ring. The obvious subclasses offer no new mechanism: triangular matrices over an algebraic division algebra are algebraic. If p kills every diagonal entry of an r by r triangular matrix W (take the product of their scalar annihilators), p(W) is strictly triangular, and p(W)^r=0. For W=[[0,x],[y,0]], W²=diag(xy,yx); if x≠0 the two diagonal entries are conjugate, and if x=0 then W²=0. These calculations do not address arbitrary matrices and are not substitutes.

There is a useful sufficient reduction with a precise missing interface. Let F be central in D and let t be an **external** central indeterminate. If R=D tensor_F F(t) is algebraic over F(t), then it is a division ring: it embeds in the skew rational-function division ring and every nonzero algebraic element has an inverse in R. Thus R equals D(t). For any W in M_r(D), tI−W is invertible over D(t), for example by its formal inverse at infinity. Its inverse then has entries in R, so a common nonzero central denominator q(t) gives

    (tI−W) B(t)=q(t)I,   B(t) in M_r(D[t]), q(t) in F[t].

Comparing coefficients from the highest degree downward expresses every coefficient of B as a polynomial in W with central coefficients; the constant equation is q(W)=0. Hence every W is algebraic. This is an elementary resolvent reduction, not a proposed new general theorem.

The source does not supply the premise. Starting its lifting over k(t) makes t part of the stage centre. Its substitutions, corrected tuple and new centre can depend on t. That does not prove algebraicity after adjoining a new indeterminate to the *final* centre. A parameter-preserving implementation would have to retain an output of the form B tensor_K K(t), with the evolving generator tuple defined over B independently of t, while correcting arbitrary t-dependent scalar expressions. The finite affine linear systems in `eq:finite-central-correction` are allowed t-dependent solutions; rank preservation under extension does not force a solution in the t-independent subspace.

The direct matrix attempt has a second exact obstruction in the contract. Replacing the input A by M_r(A) violates the division hypothesis. The source uses the fact that F[W_0] is a field to make the fixed minimal polynomial separable and the split output semisimple. For a matrix W_0 this can fail: [[a,1],[0,a]] has a repeated minimal polynomial even when a is separable. Its elementary triangular algebraicity does not extend the simultaneous spectral-response correction for arbitrary matrices. One would need a matrix-unit-preserving response/correction theorem with nonsemisimple outputs, as well as the source's generation and two-direction conditions. Neither was constructed.

The matrix direction was therefore not frozen. I have not proved that such a lifting is impossible, that all matrices over the stipulated D fail algebraicity, or that the full existential question is new to the literature. The Amitsur primary download was blocked; snippets about uncountable fields are not used as a substitute. This archive records the finite interfaces to inspect next, not a nominee with a missing bridge.

## Handoff boundary

No formalization, manuscript, release preparation, independent review, shared-index edit, git operation, nested agent, publication, contact or browser UI was used. The exact local evidence packet is sealed only for integrity. Its verifier and copied negative controls prove no mathematical theorem. No narrowed target was used to replace an unproved full target, and no contribution rating is assigned by this author.
