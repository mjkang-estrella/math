# 323512 — full ordinary deduction, excluded from discovery credit pending independent assessment

Literal source: Calcut–McCarthy–Walthers, arXiv:1205.3121v1 (14 May 2012), pp.20–24, equations (5.15), (5.16), (5.18), Lemma 5.28 and Conjectures 5.31. `deviation.pdf` and SHA256 in source-receipts.json. Actual statements AND surrounding proofs read. H<G in this paper means subgroup, not necessarily proper. Natural number in the deviation definition means positive: zero trivially belongs to every additive image and is not the intended definition.

## Exact ordinary endpoint
For every finite group G and subgroup H, with B(-) the integral Burnside ring of finite group actions and Δ the least positive integer such that Δ[H/H] belongs to Res_H^G Ind_H^G B(H),

    [G:H] divides Δ, Δ divides |G|, and Δ=1 iff H=G.

This handles all three conjuncts, not merely normal H or a finite example.

## Approach 1: augmentation and primitive idempotents (closed ordinary proof)
Write F for the family of all subgroups of G conjugate to a subgroup of H. It is closed under conjugation and taking subgroups. Let e_K be the primitive rational Burnside idempotent with mark 1 at the conjugacy class of K and 0 at all other classes. Put v=sum_[K]∈F e_K, summing conjugacy classes once.

Every subgroup of H lies in F, so the marks of Res(v) are all 1. Injectivity of the mark map gives Res(v)=[H/H]. Gluck's formula, explicitly supplied in source equation (5.15), is

    e_K = 1/|N_G(K)| sum_{L≤K} |L| μ(L,K)[G/L].

Each L in this expansion lies in F. Since |N_G(K)| divides |G|, |G|v is an integral combination of [G/L] with L in F. For each such L, choose a conjugate L'≤H; [G/L]=Ind([H/L']). Therefore |G|v=Ind(b) for some integral virtual H-set b. Restricting gives |G|[H/H]=Res Ind(b).

The integers a for which a[H/H] lies in this additive image form a subgroup of Z. It contains |G|, so equals ΔZ for a positive Δ, proving Δ divides |G|. For any a in that subgroup, augmentation (underlying virtual cardinality) gives a=[G:H]·ε_H(b), since restriction preserves cardinality and induction multiplies it by the index. Thus [G:H] divides Δ. Finally Δ=1 forces index 1 and H=G, and H=G makes Res Ind the identity and Δ=1.

No counterexample search is needed: both divisibilities have uniform proofs. The source's own normal case and Sym(3) example are consistent sanity checks, not evidence replacing this proof.

## Approach 2: direct Möbius construction (also closed; checks denominators independently)
Use the finite lattice of ALL actual subgroups, rather than conjugacy classes. Let f(K)=1 if K∈F and 0 otherwise. Set

    α(K)=sum_{K≤L≤G} μ(K,L) f(L),
    w=1/|G| sum_{K≤G} |K| α(K)[G/K].

The coefficients are conjugation invariant. At a subgroup T the mark of w is

    1/|G| sum_K α(K) #{g∈G : T≤gKg⁻¹}
      = sum_{K≥T} α(K) = f(T).

The middle equality follows by conjugation invariance and summing first over g; the last is finite Möbius inversion. If K is outside F, all L≥K are outside F, so α(K)=0. Consequently |G|w is integral and supported on F; it lies in Im Ind exactly as above. Since f is 1 on subgroups of H, Res(w)=[H/H]. This proves the same upper divisibility without importing an idempotent theorem as an unexplained black box.

## Novelty and significance limit — material, not a formalization excuse
Both arguments are short applications of augmentation plus standard mark inversion already printed in the original paper. In particular, equation (5.15), three pages before the conjectures, supplies every substantial algebraic ingredient. No new constructive mechanism beyond the characteristic family idempotent was required. Under the user's exclusion of routine corollaries this route is NOT offered for discovery credit. No public exact counterpart was found in the bounded live queries, but that is not positive novelty clearance. Palomar queries returned 403; cached revision651 receipts are unrelated and provide no target-specific clearance. Independent significance review could revisit this classification, but no self-acceptance is made.

## Lean boundary
No literal Lean theorem is claimed. A proof of the arithmetic consequence alone with mark-inversion axioms would violate the task. A full packet would need: finite G-set Burnside group, transitive orbit basis, Res/Ind and augmentation bridges, injectivity of marks, subgroup-lattice Möbius inversion or the explicit above construction, and integral induction support. This is a precise dependency frontier. Formalization was not used as grounds to abandon a new significant result; the result is screened out as a routine use of classical source machinery. No partial arithmetic helper is presented as a solution.
