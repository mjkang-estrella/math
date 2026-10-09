# H041 primary operator bridges — raw Claude report

Unaccepted proposer report; scope corrections will be recorded separately.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h041-primary-operator-bridges-opus-20261008-r1`
Provider: claudeAgent / claude-opus-5-5. Completed; no candidate supplied.

I found no new operation for H041. Under my lens (recent primary results with a concrete public ECDLP bridge), nothing produced a usable operator whose inputs come only from public data and whose recovery and costs are fully paid. So I'm submitting no candidate cards. Exponent stays at 1/2 and verified improvement stays NONE.

I made no runs, imports, edits, children or commits. I read no other H041 proposals.

**Recent results checked and why each gives nothing new:**
- **2026 ECDLP preprints:** every new prime-field ECDLP item that turned up is about reducing quantum resources: [ePrint 2026/280](https://eprint.iacr.org/2026/280), [ePrint 2026/2014](https://eprint.iacr.org/2026/2014), [ePrint 2026/1128](https://eprint.iacr.org/2026/1128.pdf) and [arXiv 2607.13816](https://arxiv.org/abs/2607.13816). None has a classical bridge. I only saw these through search results and did not open the papers.
- **Prime-field index calculus (Petit–Kosters–Messeng, PKC 2016):** this is the main primary prior art. Fetching the author's PDF ([link](https://christophe.petit.web.ulb.be/files/16PKC_primeECDLP.pdf)) failed with a TLS certificate error. I read the authors' [PKC slides](https://troll.iis.sinica.edu.tw/pkc16/slides/6-1--Algebraic_approaches_for_the_Elliptic_Curve_Discrete_Logarithm_Problem_over_Prime_Fields.pdf) instead.
  - **Their method:** the factor base is the set of points whose x-coordinate lies in V, where V is either a smooth-order subgroup of F_p^* or the x-coordinates of a smooth-order subgroup of an auxiliary curve E′. The system is Semaev's S_{m+1} plus a block-triangular chain x_{i,j+1} = L_j(x_{i,j}). They solve it with Gröbner bases.
  - **Their own conclusion:** it is practical only for very small parameters, and "Pollard's rho definitely better for crypto sizes". They leave asymptotic complexity and a dedicated solver as open problems.
  - **What I considered on top:** testing whether a point is in the factor base costs only polylog work, by applying the chain L. Under index calculus, the linear-algebra cost of p^{2/m} only drops below √p when m ≥ 5. Even then each decomposition attempt would have to cost about p^{1/m} or less, and no known operation does that. Pairing E with E′ also leads to the genus-4 fiber product that H040 already scoped. So this is PKM's open problem restated, not a changed operation.
- **ePrint 2024/1923 (Hu):** I opened only the [abstract page](https://eprint.iacr.org/2024/1923). It critiques PKM and the Momonari–Kudo improvement and asserts there is no subexponential method. That is an unreviewed single-author claim; I'm not taking it as an exclusion.
- **Galbraith–Gaudry survey, [ePrint 2015/1022](https://eprint.iacr.org/2015/1022):** I read the abstract page only.
- **Square-root Vélu product evaluation:** already covered by H019's single-query resultant. Evaluating the product over a structured giant-step family is just the interval product of size about q, at Õ(√q). It also inherits H040's ± false positive. Nothing new.
- **Alman–Vassilevska Williams 3SUM:** already recorded in H039/H017. It needs integer additive hashing, and I found no success-preserving reduction from an elliptic-curve group.
- **Other ideas that collapse into existing records or baselines:**
  - representation-technique filtering for subset sum needs a homomorphic filter (H039's coprime-homomorphism lemma);
  - higher-dimensional and polylog isogeny evaluation would need the representation of [k], which runs into H040's missing map;
  - tag tracing and x-only walk-step savings can't keep a deterministic class walk without y, a sign choice or a square root, and per-step constants are baselines.

None of this is a universal exclusion. It only says these specific routes yield no operation. A PKM-type route would reopen only if someone supplies an explicit dedicated solver for the PKM system at m ≥ 5. The cheapest test would then be how its per-decomposition cost scales with p, compared against p^{1/m}.
