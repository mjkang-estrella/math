# Statement correspondence

The Round 5A endpoint is exactly `StackSort.Cut5.commonCutCount_proved : StackSort.Round3.CommonCutCount`. The frozen Prop quantifies over every natural M,r,s with 1 ≤ M, 1 ≤ r ≤ bound M, and 1 ≤ s ≤ bound M. It asserts `literalX M r s = literalI M r s + correction false literalX literalI M r s`. No extra hypothesis, alternative count, or environmental axiom is introduced.

XI counts ordered pairs of tuples of nonempty words on labels [0,M), each flattened tuple being a permutation of those labels, whose concatenated stack-sorted outputs coincide. II adds absence of a proper positive common output boundary. The correction chooses b suffix labels, a left suffix words and c right suffix words; it counts an arbitrary remainder collision and an irreducible final block. This is the T1 common-cut shuffle factorisation in review gate C1 L7. Labels are retained in the bijection and the binomial coefficient counts their subsets.

The unchanged literal map s uses the source section 2.3 convention `s(LmR)=s(L)s(R)m` for largest m. Definition 1.1 of Defant and Propp's Quantifying Noninvertibility in Discrete Dynamical Systems defines degree as average multiplicity, `(1/|X|) Σ_x |f⁻¹(f(x))|`. The frozen deg is the literal collision count divided by M!, with the average and squared-fibre bridges proved upstream.

The source Conjecture 4.4 (arXiv v3/v4; EJC Conjecture 23) states: “The value of the limit lim deg(s : S_n → S_n)^(1/n) lies in the interval (1.68, 1.73).” The unchanged Conj and source endpoints cover its existential limit statement, lower bound on every possible limit, and explicit subsequence companion. These endpoints still require MaximumFinalCount after the present lane's theorem is supplied; they are not newly unconditional here.

The MathDB paraphrase instead calls deg the maximum fibre size. The inherited ConjMax, maximum-fibre refutation and companion address that reading unconditionally. No credit is claimed from that paraphrase. This lane changes none of those definitions or statements. The r133 draft is only historical evidence, not an imported certificate.
