# Unresolved: Brugidou's all-partition positivity conjecture

No complete eligible discovery. No acceptance nomination. No Lean claim.

## Exact source and quantifiers

Vincent Brugidou, *On a particular specialization of monomial symmetric functions*, arXiv:2306.15300v7 (4 June 2025), Conjecture 4.1. The current author abstract page still identifies v7 as latest. Actual complete HTML body was retrieved; normalizations, Corollaries 3.5–3.7, conjectures and Section 6 were read, not inferred from a MathDB label. No separate journal version was located; this is a primary preprint, not a claim of published-journal coverage.

Let Λ_Q be the symmetric-function ring, φ_q(e_j)=q^(j(j−1)/2)/j!. For every nonempty partition λ=(λ_1≥…≥λ_r>0) of n, let ν(λ)=Σ(i−1)λ_i and m(λ)!=Π_a #{i:λ_i=a}!. Corollary 3.5 defines the integer polynomial J_λ by

φ_q(m_λ)=(1−q)^(n−r) q^ν(λ) J_λ(q)/((n−1)! m(λ)!).

Its degree is d=binom(n−1,2)+r−1−ν(λ). The full target is: for **every** such λ and **every** integer 0≤k≤d, [q^k]J_λ>0. Strict positivity includes internal coefficients; positivity at positive real q would not suffice. The target is the entire all-partition statement, not another hook instance or a new finite computational bound. Unimodality MathDB 358925 led to this primary source; its open label was not used as novelty evidence. Direct MathDB HTTP returned 403; no further direct access was attempted.

## Small selection screen

Three immutable OpenAI catalogue bodies were inspected: Snaky introduction, sharp triangle-removal introduction, and unbounded Fourier singleton/degree introduction. Their principal results are already established upstream; no new explicit tractable full-scope companion conjecture was identified in those introductions. No upstream result was re-audited.

A fresh finite-object lead was Brugidou2509.20959v1 Conjecture4.3: an identity for P_λ(t)=n t^n(1+t)^ν J_λ(1+t)/m(λ)! using DFS blocks split at root-neighbors. Crucial version check: **v2 removes the entire conjectural section; the actual current author metadata explicitly says the conjecture was removed because it turned out false.** Thus a new counterexample to v1 would be rediscovery of a publicly known refutation, even if its witness differed. No census or credit work was pursued on it. The original positivity source remains a distinct all-partition target.

## Closest actual public body, classical bridge and novelty limits

At ArtificialZeng/AI-Has-Taste commit f3ae144b74f238f22c2b84b5283cb14ce912fd33, the actual manuscript *Positive initial coefficients and a positivity region for Brugidou's hook polynomials* was read in full. It proves, for K_(a,b)=J_(a,1^b)/b!, positivity through min(degree,2b+3), and full positivity if b≥max(0,ceil((binom(a−2,2)−4)/2)). It includes all hooks with 2≤a≤6 using known row cases. It expressly does not prove general non-hook positivity or all remaining hooks. None of those public results are proposed as new here.

The original source proves the row/column families, the aggregate polynomials J_n^(r), and the final n−1 coefficients, and reports verification through size43. Huh/Ardila–Denham–Huh matroid h-vector log-concavity is a powerful established bridge for actual matroid specializations; it does not identify an arbitrary J_λ with one. Source Section6 already explains that λ=(3,2,1) obstructs the direct scalar-matroid identification. Newton identities and the partition-lattice Möbius formula below are classical algebra, not new discoveries.

Current complete Omega D5, Problems, Blueprint trees were fetched. OpenAI preprints and count full trees were reused only after verifying unchanged current commit heads. A complete AI-Has-Taste tree was additionally fetched after search identified an on-point partial result. Path screens plus targeted web searches found no matching full positivity proof; this is **not** an all-files semantic search, nor worldwide novelty clearance. Toda specialization unimodality was inspected at the actual body and concerns Labelle's Cartan-data rational functions, a different object. No public Lean development was compiled or validated here.

## Independent ordinary derivation attempted

Put F_λ=q^ν(λ)J_λ, and write J_w=J_(w). For a set partition π of [r], put w(B)=Σ_(i∈B)λ_i. Inclusion-exclusion for distinct variable indices gives

m(λ)! m_λ = Σ_π (−1)^(r−|π|) Π_(B∈π)(|B|−1)! p_(w(B)).

Indeed, summing products over index tuples constant on blocks of π, the partition-lattice Möbius coefficient cancels every tuple whose equality partition is not discrete, and is one on distinct tuples. Substituting φ_q(p_w)=(1−q)^(w−1)J_w/(w−1)! yields the exact finite identity

F_λ=(n−1)! Σ_π (q−1)^(r−|π|) Π_(B∈π) ((|B|−1)! J_(w(B))/(w(B)−1)!).

This is a signed formula, not a positive combinatorial model. A hoped-for sign-reversing cancellation argument would have to pair the negative objects after expanding each (q−1)^s while preserving q-degree, with unmatched positive objects in every degree ν through ν+d. No such involution was obtained. Merely writing this formula does not solve the conjecture.

The equivalent deletion/merge recurrence gives a sharper failed-route certificate. For a=λ_r, μ=(λ_1,…,λ_(r−1)), and μ[i] formed by adding a to μ_i and sorting,

F_λ = A J_a F_μ + (q−1) Σ_i F_(μ[i]),

where A=(n−1)!/((a−1)!(n−a−1)!)=(n−1)binom(n−2,a−1).

It follows directly by splitting an augmented monomial product according to whether the distinguished variable is distinct or equals the i-th existing variable. An attempted induction separated this into qΣF_merge plus D, where D=A J_aF_μ−ΣF_merge, and hoped D was coefficientwise nonnegative. This hypothesis is false already at λ=(2,1): J_1=J_2=1, J_3=2+q, A=2, hence **D=−q**. The full F_(2,1)=q+q² is positive only after cancellation with qF_3. This is an exact counterexample to the attempted mechanism, not a conjecture counterexample.

A second shortcut, real-rootedness of every J_λ followed by Newton inequalities, fails already in the row case: J_4=q³+3q²+6q+6 has discriminant −216. Again, this is only a failed route. The source's direct matroid objection is stronger for that particular classical bridge: J_(3,2,1) has gcd of coefficients one and leading coefficient two, whereas T_M(1,q) is monic. These known obstructions must not be relabeled discoveries.

## Exact checks and strongest falsifier

`check.py` uses exact Fraction arithmetic, Newton identities for power sums, augmented-monomial deletion/merge, and a separately implemented set-partition Möbius expansion. All 66 partitions of sizes1–8 agree, have the source degree and integer positive coefficients. It reproduces J_(3,2,1)=(10,30,35,35,30,20,12,6,2), D_(2,1)=−q and discriminant −216. This is substantially below the source's existing size43 verification; it contributes no mathematical novelty. No floating-point signs or large graph census are used. Hard caps: 512MiB AS,40s CPU,50s external wall; BLAS/OMP1. See check.log and checks.json.

The strongest falsifier of the proposed proof mechanism is **D_(2,1)=−q**. Any purported repair retaining coefficientwise domination of D is invalid. A genuine source refutation would require a λ and in-range coefficient ≤0 computed from the exact specialization and independently certified; none was found. A genuine proof still requires uniform degree-preserving cancellation or a different positive representation, plus strict nonvanishing. Neither is supplied.

## Literal Lean bridge inventory

No Lean file, compile, std3 run, certificate or axiom report was produced. A complete endpoint would need (1) partitions with positive weakly decreasing parts; (2) the actual specialization or a proved equivalent recurrence defining J_λ; (3) source-normalization, valuation and degree identification; (4) coefficient positivity uniformly in λ and k; (5) coefficient and factorial/reindex bridges for the signed expansion if used; (6) a real proof of the cancellation step. Item4/6 is missing mathematically, so a formal scaffold would only hide the gap. Independent review has not occurred. No PROOF.md is supplied because no full proof survived.
