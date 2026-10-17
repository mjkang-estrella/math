# Independent contribution and eligibility review of full CS

Myeongjin Kang; no affiliation. 2026-10-17 UTC. Original prose CC BY 4.0.

**Verdict: TECHNICAL. Eligibility: no prior developed family231 target found in the bounded project-history screen. Counted=false; campaign remains 6/10.**

This is a contribution review, not a full proof PASS, a rejection of the mathematical statement, or a worldwide-priority certificate. The exact full CS scope is retained. The statement appears to extend the explicit source theorem; no primary source inspected here already states all of CS. Nevertheless, after crediting the actual primary proof operations, the remaining work is an elementary canonical exhaustion and independent-product reduction to the stipulated sampler. It does not meet this campaign's requirement of a nonroutine new contribution. No narrower replacement is proposed.

## 1. Frozen object and complete scope

The reviewed author packet is `../fresh-analytic-discovery-r18/`:

- manifest SHA256 `19e704a0677bae0015fe3b901956daef070f926ab47d7e2cd0ab63f3df38fad9`;
- candidate SHA256 `9cdb35237bd65849e6165824f3435fcaf3dc6a6e5d0ce1690221361b153f01ed`;
- original scope SHA256 `b1327efb9564d7ddf64d2bcb248aa5d70a699f3ee63ad4d364de7d5f2abc4877`.

The author read-only verifier was inspected, then run with the supplied external manifest anchor: all 31 payloads and ten pinned Git blobs authenticated. Its result proves byte identities only. I read the complete candidate, original scope, screening-before-freeze, source-reading and source-receipt files. No author mathematical diagnostic was run or used as proof.

CS asserts, for every finite or countably infinite set I, one jointly Borel map from SR(I) times [0,1]^I to {0,1}^I with exact full output law, natural under every bijection between index sets at every input. It implies factors for arbitrary permutation groups, including uncountable groups and stabilizers, and all Hermitian positive-contraction determinantal laws, with symmetry required of the law rather than a kernel representative. The empty set, finite sets and degenerate marginals are included. There is no finitary, continuous-parameter, runtime, monotone-coupling or Bernoulli-isomorphism claim. These are one target, not separate findings.

## 2. What the closest primary proofs already supply

The pinned OpenAI source is assumed true at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its truth is not audited here. The complete preprint tree lists one family231 manuscript, with all six imported section files accounted for in the author's authenticated packet.

**Alishahi–Barzegar–Zamani (ABZ), [arXiv:2203.03935v2](https://arxiv.org/abs/2203.03935v2), §§2.1–2.2.** Proposition 2.2 already proves the exact four-sign indicator covariance bound used in candidate §2. Its proof uses the increasing functions U±1_E and V±1_F. At zero cross covariances the conclusion is independence of arbitrary finite-block events, not merely independence of individual bits. Extending cylinder independence to sigma-fields and then to the countable product of components requires only the usual monotone-class argument. Lemma 2.5, via stochastic covering, gives nonnegative covariance row sums; together with pairwise negative correlation this gives the absolute row bound. The paper itself credits a more general covariance inequality to Bulinski–Shashkin and the row result to Ghosh–Liggett–Pemantle. CS should preserve that provenance. I did not independently read those earlier bodies, and make no new attribution about their exact full scope.

ABZ uses summability to remove a sufficiently distant tail in an external enumeration and proves tail triviality. It does not construct a natural sampler. Thus ABZ is not a duplicate of CS, but both the probabilistic factorization and the numerical finiteness input to CS are already supplied by its proof.

**Borcea–Brändén–Liggett (BBL), [arXiv:0707.2340v2](https://arxiv.org/abs/0707.2340v2).** Definition 2.13 supplies the finite-marginal convention. Proposition 3.1(3) supplies stable-limit closure. Proposition 3.5 proves determinantal strong Rayleighness by the determinant generating polynomial and approximation from invertible positive contractions. Theorem 4.9 uses symmetric homogenization, negative correlation and conditioning to obtain CNA+. These are antecedents, not new operations in CS. The DPP consequence in the source already uses finite compressions and inclusion–exclusion, allows complex Hermitian/singular/projection kernels, and distinguishes law invariance from kernel invariance for regular actions.

**Pinned family231, actual proof bodies.** `lem:sr-response` proves the uniform 1/2 response for all finite positive tilts, including nonhomogeneous and degenerate laws. `prop:brownian-sampler` accepts any countable index set and finite site-centered exhaustions of that entire set. It already proves exact full joint output law using the observation process, innovations, deterministic inversion and integer-time slopes. `lem:inverse` already gives all-input existence, uniqueness, Borel measurability, factorial Picard bounds, and intertwining under bijections between different index sets. The Brownian converter in `lem:edge-noise` is likewise defined on every input.

The source's `prop:canonical-drift` and implementation section use intrinsic finite graph balls, finite tilt ratios, limsup, parameter integration and Picard iteration to obtain one Borel rule on varying graphs. The general SR theorem chooses translates of an external finite exhaustion of the regular group. The source expressly does not claim arbitrary actions because such exhaustions are not automatic. That limitation is real; it is not evidence by itself that every way of removing it is a substantial new theorem under this campaign's standard.

**Lyons–Thom, [arXiv:1402.0969v2](https://arxiv.org/abs/1402.0969v2), §7.** Their relatively independent joining construction and Lemma 7.2 turn invariant monotone couplings into d-bar bounds. Lemmas 7.8–7.9 obtain norm/Schatten continuity through operator interpolation and spectral truncation. Theorem 7.3 uses Kaplansky density to approximate by finite-range kernels; Corollary 7.4 adds amenability and Bernoulli closure. Questions 7.5–7.7 explicitly separate finitely dependent approximation, closure of factors, and the determinantal factor question. These are not the pointwise law-parametrized construction of CS. This comparison rules out a false duplicate verdict from the words “determinantal factor”; it does not award CS the sampler mechanism already paid by the newer stipulated source.

The family236 companion's actual introduction/main theorem concerns the sharp free Ising range on regular trees. Its geometry is given, and its conditional-copy recovery differs from the uniform-response inverse. It is not CS. This review read that introduction, not the companion's full critical proof.

## 3. Explicit residual reduction, preserving every CS quantifier

Here is the operation left after the antecedents above, stated independently of strongly Rayleigh terminology. This makes the TECHNICAL classification checkable rather than an assertion that a short proof must be unimportant.

Suppose a law on a countable binary product has a symmetric, nonnegative, Borel law-derived weight w(i,j), invariant under relabeling, with finite row sums. Suppose its positive-weight components are independent factors, and each component marginal satisfies the given sampler's finite-tilt Lipschitz hypothesis. The following generic recipe removes all external geometric choices.

For each integer n≥1 put an edge ij when w(i,j)≥1/n. At vertex i the number of such neighbors is at most n times its row sum, hence finite. The radius-n ball B_n(i) is finite: induct on the radius, taking finite unions of finite neighbor sets. Both thresholds and radii increase in the appropriate direction, so the balls increase. Every finite positive-weight path is contained in some sufficiently large threshold graph with path length at most n. Hence the union of the balls is exactly the positive-weight component.

For each fixed i,j,n, ball membership is a countable union of finite conjunctions of Borel edge predicates. The finite-subset-valued ball map is therefore Borel: its equality to a specified finite set is a countable conjunction of membership and nonmembership conditions. Relabelings transport it exactly, at the same n; no random choice or enumeration is present in the formula.

Apply the already-proved sampler separately to each component using these balls. Define the construction globally by the same finite-tilt/limsup/Picard formula. The drift at a coordinate reads only its component, so induction through Picard proves that the global solution restricts to the component solution. Independent input families give independent output components, and their known marginal laws give the complete joint law. No measurable enumeration of components or representatives is needed.

Finally, countable piecewise finite-tilt formulas are jointly Borel in the law and fields. Parameter integration and rational-time path evaluations propagate this through the same Picard iteration already used in the source. Exact transport of finite balls gives exact transport of the drift, and the source inverse and coordinatewise converter/readout give all-input naturality under every bijection. Arbitrary group size adds no new intersection-of-null-sets issue: each equality is a pointwise identity of those formulas.

For CS use w(i,j)=−Cov(X_i,X_j). ABZ/BBL and the source response provide every hypothesis just listed; their row bound even improves the generic local finiteness to degree≤floor(n/4). ABZ's zero-cross inequality supplies independent components. Strong Rayleighness passes to their marginals, and the source finite-tilt estimate supplies L=1/2. Determinantal laws enter by the already-paid BBL/source reduction.

Thus the new residual operation is exactly the elementary threshold-ball construction plus independent-product assembly. It does not need a new response estimate, a different inverse, a new stochastic coupling, or a new way of sampling across dependent components. Joint Borel dependence adds standard parameter bookkeeping already illustrated in the source's varying-graph proof. These statements cover the full frozen target; they are not a reduction of the target to a smaller action class.

## 4. Why the obstruction example does not change the verdict

The infinite equal-parameter Bernoulli product has full permutation symmetry. A finite set containing i and invariant under its full stabilizer cannot contain any other site, since the remaining sites form one infinite orbit. Therefore there is no stabilizer-invariant finite exhaustion of the whole index set. This correctly shows that merely choosing a better global exhaustion would fail.

CS bypasses that issue by discarding whole independent components, here singletons. That is mathematically useful. But the permission to discard them is precisely the zero-cross-covariance independence conclusion already supplied by ABZ. Within a component, thresholding a summable invariant weighted graph is the elementary mechanism above. The example establishes a genuine scope difference from the source's regular-action theorem; it does not introduce an additional unpaid operation beyond the displayed reduction.

Likewise, the even-parity countercontrol correctly shows why pairwise decorrelation alone is insufficient. The needed higher-event inequality is not new in this candidate. Its necessity is not evidence of new proof content when its complete proof is inherited.

## 5. Eligibility, search limits and decision

The original review brief and operative history/exclusion passages were read, with the supplied r15/r17 reference chains retained. Current and earlier TEN/TWENTY ledger acceptance standards and relevant history entries were inspected. A targeted body search of root iteration reports and all three ledgers for strongly Rayleigh, FUSF, Lyons–Thom, covariance components and free uniform spanning forests produced only the relevant I77 finite matroid-sampling comparison. Its target is weighted degree-preserving switch-chain mixing; reading its actual source comparison and beginning of the construction confirms that it does not develop infinite-law natural coding. I also read the full I09 Potts FIID report: its families229/236 and unpaid multistate response estimate are distinct from family231's negative-dependence construction. Searches of current campaign candidate/analysis bodies outside private/input trees and the current CS work found no prior target. Exact commands/results are in `history-search.json`.

This is bounded affirmative eligibility evidence, not a claim that every nested historical archive or every unrelated ledger paragraph was read line by line. No older developed CS target was identified. The candidate should not be rejected as INELIGIBLE based solely on the shared word “sampling” or the old Ising/FIID tracks.

Six bounded web queries checked SR equivariant sampling, covariance graphs and arbitrary-action determinantal factors. They located no actual primary statement of full CS. Absence of a search hit is not novelty evidence. One broad description of the pinned Lean supplement warranted a direct check: the actual `StronglyRayleighDPP.lean` comparator quantifies arbitrary countable sets only for DPP existence/uniqueness; its factor predicates use the regular group action. It therefore does not duplicate CS. The declaration file is a comparator statement file, not a proof audit. New retrieved primary bytes and URLs are retained privately with hashes.

**TECHNICAL is the resulting campaign verdict.** It is not DUPLICATE, since no sufficient antecedent statement of full CS was identified; not INELIGIBLE, given the bounded history check; and not UNRESOLVED merely because worldwide priority remains uncertified. The operational contribution judgment is supported by a complete reduction to paid ingredients. A correct and potentially publishable extension can still fall below this campaign's substantiality threshold. Preserve the frozen full theorem and the separate proof review, do not count it toward ten, and do not split its arbitrary-action, Borel-parameter and DPP consequences into substitute nominations.

No author/shared files were edited; no nested agent, staging, commit, manuscript, formalization, publication or submission action was performed.
