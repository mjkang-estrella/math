# Scope and operation comparison

Author-side assessment only. No independent contribution verdict, nomination, count, or worldwide priority claim.

## Direct Fourier antecedents

[Filmus–Hatami–Keller–Lifshitz, arXiv:1404.3396v3](https://arxiv.org/pdf/1404.3396v3): actual Lemma3.10 proof symmetrizes into bounded real-valued functions and bounds the linear sum by degree. Lemmas3.14–3.15 similarly preserve influence for monotone real-valued symmetrizations. These do not preserve Boolean values. Conjecture3.17 is the general Boolean square-root bound; §3.5/Proposition3.18 uses equal coordinate influences and hypercontractivity to bound transitive functions' variance/influences in terms of degree and dimension. It does not impose the square-root linear bound on that subclass or identify its cyclic restriction as a separate obstruction. Our construction does not improve Proposition3.18 or resolve the monotone specialization.

[Jha, arXiv:1611.01029v2](https://arxiv.org/pdf/1611.01029v2): the complete two-page body rewrites the sharper majority benchmark using positive/negative discrete derivatives. There is no cyclic construction or transitive restriction. These identities do not provide the missing event-valued symmetrization.

Wang's ePrint2020/002 and Kudin–Pašalić's degree4 counterexample are credited through the pinned manuscript bibliography/introduction. Their full bodies were not obtained: ePrint PDF403, current university thesis URL404, old university URLs401, repository403. Indexed abstracts are not treated as proof-body reading. This limits any literature novelty claim.

## Closest actual symmetry-construction bodies

[Chakraborty, DMTCS13:4 (2011), 51–60](https://dmtcs.episciences.org/552/pdf): §§2–3 define minterm-cyclic orbit unions, modify Rubinstein's example, and construct a marked cyclic pattern whose overlap constraints control sensitivity. The stated applications answer Turán and Kenyon–Kutin sensitivity questions. This is an actual antecedent for enforcing cyclic symmetry by shifted patterns with controlled compatibility. Its construction does not provide our source's cancellation-based coordinate-order saving or Gaussian conditional-sum variance. Our new step is the very simple special case in which all shifted role patterns are incompatible, preserving the source event's conditional law exactly.

[Chakraborty–Kayal–Paraashar, DMTCS27:2 #18 (2025)](https://dmtcs.episciences.org/15992/pdf): Observation2.50 proves preservation of transitivity under composition using wreath products. §§4.1–4.3 construct an encoded pointer function, couple pointer updates to cell permutations, prove bit transitivity generator by generator, and transfer degree/query bounds with logarithmic encoding cost. This establishes that symmetry-preserving separations are a serious established research theme; proof length alone cannot dismiss our strengthened scope. It also credits our wreath-product step as standard. Their transfer controls query complexity and polynomial degree, not the uniform signed linear coefficient sum. §7's explicit open problems concern cheat-sheet, approximate-degree, HEX/EAH, and listed combinatorial-measure separations. None is settled by our consequence.

[Savický, ECCC2013/191 revision2](https://eccc.weizmann.ac.il/report/2013/191/revision/2/download): the first75 extracted lines distinguish weak coordinate symmetry from a different vertex-transitivity notion involving cube isometries. Its abstract's polynomial degree is over GF(2). Screened out at this definition check; not used as a theorem or proof comparator for real Fourier degree.

[Long, arXiv:2610.09725v1](https://arxiv.org/pdf/2610.09725): introduction and actual low-degree projection/jump estimates through Theorem4.1 and the start of the transitive specialization were read. The method combines small jumps of fixed-degree projections, a reversible mixed-jump second moment, and tameness to force vanishing variance. It neither transfers arbitrary Boolean functions to transitive functions nor supplies a static square-root linear-coefficient bound. Our construction makes no tameness claim and does not resolve a remaining question in that paper.

## What the stronger scope establishes

The exact consequence says the linear-coefficient/degree violation persists when every input position is equivalent under a single cycle. For such f all singleton coefficients equal a>0, and L(f)^2=n W_1(f). Thus it is equivalently an unbounded ratio nW_1(f)/deg(f) within the cyclic class. This is an interpretation, not a second finding.

There is a genuine distinction from full symmetric Boolean functions. If nonconstant symmetric f has degree d, its univariate Hamming-weight polynomial p takes values ±1 at n+1 distinct points. The nonzero polynomial p²−1 then has at least n+1 roots, so 2d≥n+1. Cauchy–Schwarz gives L(f)≤√n<√(2d). Consequently full permutation symmetry forbids unbounded ratios, whereas cyclic symmetry does not. This elementary contrast motivates the restriction, but does not establish that it was a separately recognized open problem.

## Assessment against the campaign gate

Evidence FOR significance: transitive/cyclic classes are established, not invented for the result; symmetry can genuinely improve relations; generic total-function symmetry conversion is not available in the 2025 proof; fully symmetric functions satisfy an elementary constant bound; the source's role asymmetry is removed while retaining arbitrary factors.

Evidence AGAINST substantial nomination: no separately posed cyclic/transitive linear-Fourier question or known failed approach to that restriction was identified; none of the explicit transitive separation problems above is answered; the source supplies the entire conditional-variance advantage and arbitrary amplification; the only new ingredient is disjointness of its already-separated leaf intervals under shifts, followed by standard equivariance and composition. No new asymptotic tradeoff, quantitative dimension bound, or monotone result is proved.

**Author recommendation on current evidence: preserve the complete every-C consequence as a technical pre-freeze result; do not nominate it solely because the class restriction is natural or the exact statement was not found.** This is based on the unpaid mathematical content and scope comparison, not solely proof length. The parent may commission separate contribution review; this recommendation is not an independent verdict.

## Bounded search limits

Searches covered combinations of Gopalan/Servedio, signed/linear Fourier coefficients, cyclic/transitive/weakly symmetric, real degree, and Boolean functions. Primary bibliographies and proof bodies above were inspected at the recorded extents. Cryptographic GF(2)-degree/linear-structure results, polynomial-threshold degree, rational degree, and sensitivity statements were distinguished from our parameters. No exhaustive literature search or worldwide novelty claim is made. Absence of a located separate question is a limitation of this bounded screen, not proof that nobody asked it.
