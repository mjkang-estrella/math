# H10(Q): integrated finite-test compression investigation

PREFREEZE / no nominee. This is a research derivation and strongest-reduction comparison, not a frozen theorem, submitted supporting result, manuscript, correctness verdict, contribution verdict, or acceptance. One developed family is Source004. All pinned source operations are stipulated true. The investigation seeks a new operation after those operations; it does not audit their truth.

## 1. Exact interfaces and the explored strengthening

Let A be the set of integer polynomials, in arbitrary finite numbers of variables, having an integer zero; let B be the analogous rational-solvability set. Effective codes retain arbitrary degrees, coefficients, and variable counts. Source004 October6 `thm:main` proves B undecidable, and `thm:degree-normal-form` proves B has Turing degree0′. Its latter proof gives computable many-one equivalences with rational solvability of quartics and presented sums of squares of quadratics. Its reduction A≤T B is explicitly not asserted to be many-one.

The explored strengthening is whether one can construct a total computable map f↦G_f of integral polynomials with

    f∈A iff G_f∈B.                                      (1)

Equivalently one could construct a single rational-polynomial encoding of halting by composing with the classical integer DPRM representation. No bound on output variable count, degree, coefficient height or witness multiplicity is proposed. No existential definition of Z in Q is assumed. This is a prefreeze feasibility question, not a renamed or frozen conjecture and not a submitted full claim. No proof of (1) was obtained.

Actual source reading preceded this note: full introduction, full reduction, full elliptic rank/formal-log section and consequences; parity soundness, global-point realization and final assembly; prime-witness/CRT assembly; modular-height endgame; rational-two-torsion companion statement and its final proof assembly. Acquired internal sections are not thereby read. Primary comparison uses actual Miller2021 §§5,6.1 proofs, especially Lemmas6.1/6.3 and Theorem6.5. Transitive proof coverage is bounded in READING.md.

## 2. Pay every finite logical and polynomial operation first

The source effectively generates a sequence of finite rational constraints T(f,n), with the same fixed arithmetic data for every input. They can be made cumulative. Every constraint is an existential Boolean combination of polynomial equalities/inequalities once the finite Skolem ground terms and the witnesses for the positive existential Φ have been introduced.

For each finite test, first put negations at atomic level. Replace g≠0 by gy−1=0. Separate disjuncts into independent blocks of existential variables; a conjunction of residual equalities is one equation Σ_j q_j²=0 over Q. For finitely many disjuncts with polynomials H_i on independent blocks, ∏_i H_i=0 is equivalent to at least one disjunct being solvable: extend a solution in one block by arbitrary rationals in the others. Empty true/false formulas are respectively the equations 0=0 and 1=0. Clear fixed rational coefficients. Thus each T(f,n) is equivalent to ONE rational polynomial equation g(f,n)=0, not merely a finite list of oracle queries.

The cumulative sequence satisfies

    f∈A iff (∀n∈N) g(f,n)∈B,                           (2)
    g(f,n+1)∈B ⇒ g(f,n)∈B.                            (3)

For fixed f,n the map is computable. The finite constants in the source, even where their initial choice is ineffective, are fixed exact algebraic/rational data and finite integers and can be hardcoded. Their nonuniform selection is not a justification for asserting no computable map exists. All reduction claims here concern existence of a single machine after these fixed choices.

Every individual g can already be converted to degree≤4 using the source circuit construction. Give each arithmetic gate a new variable, impose its linear or quadratic gate residual, and sum the squares. Each actual input has a unique extension to the circuit gate variables. This handles conjunction, disjunction and inverse variables compatibly, at the price of more variables. It does not impose smoothness; no old smooth-quartic target is silently changed.

A positive finite truth-table reduction to B would also collapse by exactly these operations: express its monotone Boolean formula through the sum-of-squares AND and independent-block product OR. Therefore finite positive Boolean complexity is completely paid. A general oracle trace includes negative answers (“this polynomial has no rational zero”), which are not supplied by a rational point. Dropping them can admit accepting transcripts inconsistent with the true oracle. This observation is only a limitation of that trace translation, not a proof that (1) fails.

An especially concrete SUFFICIENT bridge would be a total computable N(f) for which

    g(f,N(f))∈B ⇒ f∈A.                                (4)

The reverse implication is already true for every test. Under (4), G_f=g(f,N(f)) proves (1), and quartic normalization gives the same reduction to quartics. No necessity claim is made: a different many-one reduction need not select one of the source tests. Source compactness proves that SOME failed n exists on every no-instance, not that such an n is computably bounded in f before an oracle is queried.

The source oracle algorithm is stronger than a bare undecidability contradiction: enumerate integer zeros while querying the cumulative tests until one fails. Each branch is sound and one branch terminates. But the fact that the realized computation asks finitely many queries on each input does not give a computable advance bound or (4).

## 3. Integrate the arithmetic proof at one fixed precision

It would be too weak to stop at saying “compactness is ineffective.” The source has strong uniform arithmetic information that must be retained.

It fixes F=Q(√2), d=75−53√2 and E:y²=x³−d²x, and chooses m and a nontorsion P with mE(F)=ZP. The actual elliptic section computes rank one by dual two-isogeny descent, retaining the dyadic and norm-seven valuations. Its formal group proof computes finite logarithm truncations ℓ_K and proves uniform index-ratio valuation and truncation congruences away from finitely many primes. No infinite series is evaluated in a nonstandard structure.

If all finite tests succeed, source `red:compactness` builds a model R of the whole recursive theory in an elementary extension *Q of a many-sorted arithmetic structure. The attached points give an additive injection η:R→*Z with η(1)=1 and T_a=η(a)P. Multiplicativity is NOT assumed. Every ring value satisfies Φ; its auxiliary rational witnesses are not themselves added to the term ring.

At a fixed ordinary precision K, every A∈R has a three-slope representation A=u1/v+u2/v+u3/v with thirteen contact-form factors εkr. Every r has a field quotient R/rR and two tested residue branches. At each branch one pair h,j0 is fixed for all a∈R. The source CRT proof gives those compatible witnesses in the ordinary integer model; it is not a separate witness chosen after a particular root coordinate.

At a contact prime q, an odd valuation of one r selects a coarsened valuation center. The paired tests then give, for all a∈R,

    V_a=η(ha) ≡4η(a) mod q^K,
    V_1 ≡4 mod q^K,
    a~ ≡ V_a/V_1 ≡η(a) mod q^K.                       (5)

Here the conjugate-curve condition supplies the first line using additivity; V_1 is a unit because q≠2. Only THEN is the primary logarithm ratio theorem applied with integral ratio. This pays the compatibility that a one-curve formal-log argument would miss.

For the modeled root tuple set δ=f(η(a1),…,η(an)), B0=max(1,|η(a1)|,…), D=max(1,deg f). If δ=0, elementarity already gives an ordinary integer solution. Otherwise |δ|≤C_f B0^D. Choose ONE ordinary K≥cD, where c is the fixed height exponent, enlarged to an integer. All contact primes for all three-slope representations divide the SAME δ to order≥K by (5). The finite-product transfer gives

    M_K(s_i)^K | δ,
    h(s_i) ≤ H_K M_K(s_i)^c ≤ H_K C_f^(c/K) B0^(cD/K),
    h(A~) ≤3 H_K C_f^(c/K) B0 + log3                  (6)

for EVERY A∈R. Fixed exceptional primes change H_K, not c. Both endpoints of the comparison are retained; “finite precision is absent” would be an incorrect diagnosis.

Apply (6) to the three ring coordinates representing x(T_aj). Standard height inequalities over fixed F yield h(x(η(aj)P))≤C B0+C′. Canonical height gives h(x(nP))=2 hhat(P)n²+O(1), hhat(P)>0. For a maximizing nonzero index,

    2 hhat(P) B0² ≤ C B0+C′.                          (7)

Thus B0 is ordinary bounded. All η(aj) are ordinary integers; additivity and injectivity identify aj with them, yielding an integer root. None of this needs a common numerical rank-one witness in a varying field, integral splitting of Selmer groups, or a new BSD transfer.

Crucially, (7) is obtained in the δ≠0 branch. In the δ=0 branch the proof immediately transfers existence of an integer root; it provides no bound on the size of the least integer zero. Reusing the δ≠0 bound as a universal search bound on integer roots would be invalid. The same caution applies to a finite partial assignment, where η may not even be defined on a whole ring.

## 4. Where finite closure remains unpaid

Fixing K does not make the source theory finite. It retains arbitrary ring terms, field-quotient axioms, the common branch witnesses for all a, and Φ on every ring value. Merely keeping root variables and their elliptic coordinates does not retain those facts automatically.

In `red:coarsening`, J is the convex subgroup of *Z generated by negative valuations of nonzero elements of the embedded R. If v(a)∈J, the proof uses products of negative-valued ring elements to find b∈R with v(b)<−|v(a)|. Both b and ab then have negative valuation, so Φ on BOTH implies v(a)=v(ab)−v(b) even. Hence odd v(r) lies outside J and positively survives in *Z/J. This uses closure and parity of the ring; it is not a finite formal-log approximation issue.

The resulting nonnegative valuation on R[√2] has a prime center above r. Because R/rR is a field and X²−2 has two distinct residue roots, that center is exactly one of the two tested ideals. Denominators outside that center become valuation units after coarsening. The source may then transfer membership r^l X/Y to the required ambient lower valuation bound. A finite selection of equations must justify this same localization behavior; simply omitting denominator conditions does not do so.

The following small calculation isolates a limitation of a proposed shortcut. Given N≥0 and a prime p outside the fixed exceptions, put a=p^(−2), r=p^(2N+1). For j=0,…,N,

    v_p(a^j)=−2j,
    v_p(a^j r)=2N+1−2j>0.

Every displayed negative valuation is even, yet v_p(r) is positive odd. At j=N+1 the second valuation becomes−1. Thus bounded samples of products cannot, using ONLY the negative-even-valuation consequence, replace all products used to form J. This is not a model of the actual finite tests: actual Φ is stronger than its stated one-sided necessary condition, and its truth on these rationals is NOT asserted. Nor does the calculation exclude clever finite witnesses or different compatible arithmetic constructions.

A related finite-substitution attempt also fails at this limited level. Let R1,…,Rt be nonzero rational functions of one variable, write Ri=Ai/Bi with rational polynomials, and choose p so all coefficients are p-integral and all leading coefficients are p-units. This excludes finitely many primes. If v_p(x)=−2m<0, the leading monomial of each nonzero polynomial has uniquely smallest valuation: for j<d,

    v(c_j x^j)−v(c_d x^d) ≥2m(d−j)>0.

Consequently Ai(x),Bi(x) are nonzero and

    v_p(Ri(x))=−2m(deg Ai−deg Bi),                    (8)

which is even. Applying the pole-parity CONSEQUENCE to finitely many rational-function substitutions therefore cannot alone detect these even poles. This includes finitely many integer shifts and fixed powers. It does not cover arbitrary existential elliptic witnesses or prove Φ itself unable to define a stronger set.

One could seek finite witnesses certifying the necessary localization closures, or a direct positive polynomial encoding bypassing them. Neither was built here. The exact residual is (4) for this compression route, or another proof of (1) with both directions and total effectivity. The diagnostics (7)–(8) are not substantial evidence or a supporting nominee.

## 5. Stronger primary composition: conditional integer definition

Russell Miller, HTP-Complete Rings of Rational Numbers, arXiv1907.03147v2 (17Nov2021; paper dated19Nov2021), Lemma6.1 gives a compatible normalization stronger than ordinary denominator clearing. Suppose an existential polynomial g(x,z1,…,zj)=0 defines precisely Z inside Q. Set

    D(t)=1+t1²+t2²+t3²+t4²,
    h(x,y,t)=D(t)^d g(x,y1/D(t),…,yj/D(t)),           (9)

where d is at least the total z-degree and fixed rational coefficients have been cleared. D never vanishes on Q. For integer x with rational witnesses z, take a positive integral common denominator v and use four squares for v−1. Then t,y=vz are integral witnesses for h. Conversely, any rational witnesses for h yield rational witnesses for g, forcing x∈Z. Hence the same h defines Z with integral witnesses on integer inputs and works over every subring of Q. This is the actual primary proof, not an inferred abstract consequence.

With that hypothesis available, translate all integer unknowns in f using h and combine the equations by squares. This proves (1). Miller6.3 pays the further passage from many-one to injective reductions by a fresh-variable even-power padding (using exponent2(n+1) if inputs begin at n=0). Source quartic circuits pay degree normalization afterwards. These operations are mutually compatible; failure of a naive finite test is not an objection to this conditional composition.

But source Φ does not have the required exact soundness “Φ(x)⇒x∈Z”; it only excludes negative odd valuations away from finitely many primes. Its all-integer completeness cannot be substituted for that stronger hypothesis. Nor does abstract Turing degree0′ itself supply the polynomial g in (9). The primary's historical open-status prose is not adopted as a current-worldwide claim; its actual proven conditional operations are what is used here.

## 6. Historical and contribution boundary

F003 already packages source H10 into rational singular points of normal rational quartics, with explicit dense smooth chart and unbounded dimension. Arithmetic14's actual first section develops the Poonen/Bertini/adjunction transfer to canonically polarized varieties and declines it as technical. T004Q63's frozen scope is globally smooth geometrically integral affine hypersurfaces of degree≤4, with variables and heights unrestricted. Its actual original proof-attempts preserve that scope, derive a degree12 smoothing and record why universal quadratic aggregation and aggregate-linear guards fail. All these scopes/proofs/dispositions remain unchanged. No higher-degree, singular-locus, projective, restricted-input or fixed-dimension substitute is proposed here.

The present one-family investigation pursues an arithmetic/logical compression operation, not that smoothness problem. It achieves only the strongest source/classical reduction (2)–(9) and a precise finite-closure obligation. It does not establish many-one completeness, an existential integer model, a uniform finite cutoff, a new theorem, or impossibility of any of those. Failure of these two parity-only shortcuts does not defeat compatible operations retaining the full Φ and elliptic data.

No theorem was frozen because full feasibility did not close. No independent correctness/contribution grade, acceptance, count, priority, literature exhaustion or current-open claim is assigned. The parent alone may integrate/review/count; this packet supplies no full author-proof nominee and no supporting nominee.
