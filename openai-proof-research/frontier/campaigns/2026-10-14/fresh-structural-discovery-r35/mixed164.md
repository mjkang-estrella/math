# Family 164: mixed read-once integer patterns remain unresolved

## Exact full question retained

For every r,k≥1 and every coloring χ:Z_{>0}→{1,...,r}, do there exist distinct positive integers a1<...<ak such that **every** read-once arithmetic expression built using binary + and × from any nonempty subset of these k variables has the same color? Each selected variable occurs once; arbitrary binary expression trees are allowed. Singletons, finite sums, finite products, xz+y, yz+x, and (x+y)z all belong to the target. No infinite sequence, subtraction, constants, repeated variables, prescribed color, or additional growth condition is requested. “Sums of disjoint products” is only a subclass: expanding (x+y)z repeats z across monomials.

This was a research question and was not frozen as a proved candidate. The pinned source's finite FS∪FP theorem, its separation strengthening, distinct-expression and prescribed-divisibility companions are already supplied and are not new nominations. Earlier arithmetic-r1 work on 164 was only a prescreen, not a developed theorem. The full question above was not replaced by a rational or ordered-block statement.

## A positive algebraic lemma, with its limits

The following is a specialization of the source's `lem:finite-word-plan`, using its finite nilpotent recurrence and backward protection. It does **not** assert an integer realization.

Fix a pivot i. A target is B=T∪{i}, with T⊆[i−1] (the empty tail is allowed). Each target has a finite collection E_B of nonempty adding sets A⊆[i−1]. For this abstract lemma there is no disjointness or ordered-tail requirement. For a group of nilpotence class at most s acting on X, assign a generator L_(B,A) to each pair and an arbitrary finite palette C_(B,a) to every positive rational leading index a. As in the source, a word letter at scale b is interpreted as

    ((U,A),γ)[b] = L_(U,A)^(q0 γ b_A/b_U).

For prescribed finite future multiplier lists, there are finite rational scale/update/word lists and a common denominator q0, independent of the numerical generators and palettes, that realize all the source terminal own-letter palette comparisons. All actual letter powers are integers. The same assertion holds over finitely many pivots, with earlier centers left unchanged when later pivots execute.

**Proof.** Order the targets B_j=T_j∪{i} in nonincreasing |T_j|. At its update use

    b_l' = k b_l (l<i),  b_i'=k^(−|T_j|)b_i,  b_l'=b_l (l>i).

This fixes b_(B_j). For e=(C∪{i},A), the ratio b_A/b_(C∪{i}) is multiplied by k^λ where

    λ = |A|−|C|+|T_j|.

Perform exactly the source backward recursion on requirement lists. Its essential additional invariant is this: the word list that must be handled by recurrence **for target j at stage j** only uses generators attached to targets j,j+1,...,q. At the terminal stage each target has only its own letters. Recurrence for target j chooses its jump J in the subgroup on the letters in that target's required words. Consequently J has no labels before j. When propagating requirements for an earlier target l<j, inflate the earlier words, and append J; neither operation creates a label before l. Backward induction proves the invariant.

For each generator relevant to recurrence at j, its tail C has |C|≤|T_j|. Since A is nonempty, λ≥|A|≥1. Thus the inflated words are ordered products of fixed abstract generators to integer polynomial powers ±k^λ vanishing at zero. The source finite nilpotent recurrence applies. When an earlier target's predecessor budget is computed for a **fixed finite alternative k**, an inflation exponent may be negative; this is harmless, since it merely changes a rational word coefficient. Positivity is needed only for the current recurrence family, not every letter of every predecessor budget.

For every earlier B, retain both the jump J and each inflated word I_k(w)J, together with the changed leading multiplier. Both palettes agree with the same old center; transitivity gives the required comparison at the jumped center and new scale. This is the source preservation argument, with no commutativity assumption. Finiteness is preserved under all unions and products. Plan pivots in reverse order to enumerate future multiplier tuples, then execute them forward. Finally enumerate the finite scale paths and clear all rational letter exponents with q0. This choice changes only the interpretation homomorphism of the abstract generators. Auxiliary slot budgets are finite by enumerating word prefixes. ∎

The nonemptiness of A matters: when A is empty and |C|=|T_j| the exponent is zero. Arbitrary target order also does not suffice: with |T_j|=0, |C|=2, |A|=1 it is −1. These are checked explicitly in `checks.py`.

### Actual primary comparison: the mechanism is paid

[Hunter, On a method of Alweiss](https://arxiv.org/abs/2308.10749), Lemma 7.4 and Remark 8.8, uses the degree condition |A|+|S|>|B|. Proposition 8.2 builds future-composition stabilizers backward. Section 9 nests the remaining shift families when extending to sums of disjoint products. Thus positive-degree rescaling plus future-support protection is already a primary operation. The retrieved version labels the latter result a sketch and omits some details; it is not used here as a completed integer theorem. The proof above obtains its noncommuting recurrence from the stipulated source and gives its own support invariant. This specialization remains TECHNICAL. Alweiss's [§4 Proposition 4.1](https://arxiv.org/html/2307.08901v5) supplies the preceding compensating-scale mechanism; rational division there does not provide the integer sampling bridge needed below.

## Exact simultaneous-scale obstruction

In the source, output block values have scales h_B b_B t_B, where h_B is a product of individual smooth integer h_l, the rational b's lie in fixed finite lists, and the h_l are multiples of W^w. Its normalized displacement for adding block A to anchor B is (h_A b_A)/(h_B b_B)·t_A. Admissibility makes the scale ratio an integer with strong W-divisibility, before the W-unit raw variables are sampled.

Take three disjoint selected blocks x,y,z with z as latest pivot. To treat xz+y with anchor xz and yz+x with anchor yz, the unchanged simultaneous admissibility demands the ratios

    R1 = h_y/(h_x h_z),    R2 = h_x/(h_y h_z)

both be positive integers (in fact highly W-divisible). But R1 R2=1/h_z²<1 whenever h_z>1. They cannot both be positive integers. For fixed positive rational block multipliers b_x,b_y,b_z the product is 1/(h_z b_z)², still <1 eventually. A fixed finite palette of possible b_z cannot repair this as w→∞. This argument also applies when x,y,z themselves represent disjoint products of raw variables, by multiplying their h- and b-scales.

**Scope:** this rules out imposing both of those original scale requirements on one final h-tuple. It does not refute monochromatic read-once patterns, arbitrary integer model normalizations, or all sequential/auxiliary constructions. It does not even refute alignment inequalities obtained by a different mechanism without integral normalized shifts.

The precise source realization needing this condition is §08's integer-residue setup: q_e=(h_A/(q0 h_U))t_A is integral; choose t_C r_e≡q_e modulo MW^w; form Δ_e=(q_e−t_Cr_e)/M. The identity

    t_C(p+m r_e)+m M Δ_e = t_Cp+m q_e

then lifts own-letter words to model evaluations. High W-divisibility makes raw slot shifts preserve the W-unit sampling law and makes Δ_e divisible by every eventual fixed local period. The abstract word lemma does not supply any of this arithmetic.

## Concrete attempts to bypass it

**Sequential h-tuples.** One can satisfy R1-integrality at one stage and R2-integrality with a different h-tuple. The product obstruction does not apply across two different stages. However, to obtain the full target both comparisons must concern the same final a_x,a_y,a_z. The actual source keeps h and all raw variables fixed before alignment. Its later-stage protection enumerates only finitely many rational b-multipliers; it does not allow new w-dependent h-ratios, replacement model families, or resampling previous variables. A stage-dependent construction would need a uniform transport of prior comparisons to the new models and a positive conditional mass bound through all stages. None has been proved here. Merely relabeling h-changes as b-changes breaks the finite-list quantifier.

**Auxiliary independent monomials.** Introducing u=xz and v=yz would make xz+y and yz+x look linear in auxiliary variables. But the required identities force xv=yu, as well as the common quotient z. Independent sampling does not enforce this. Even on [1,N]^4, the relation xv=yu has probability at most 1/N: fixing x,y,u permits at most one v. Thus the source's unrestricted product-law prediction cannot simply be conditioned on this locus with a positive density independent of scale. This is a barrier to that direct independentization, not to every dependent-variable model or fiberwise construction.

**A common smooth normalizer.** Replacing each χ(h_B·) by a model of χ(H·) with H dividing all h_B and h_A makes the desired additive arguments integral. But the anchor is now (h_B/H)t_B. Its progression step has the smooth factor h_B/H; §08's rough-step comparison removes W-unit tail factors, not an unbounded smooth multiplier. Translation by h_A/H may cross the fixed smooth-residue cosets of this progression. The old face-invariance theorem therefore cannot simply be invoked. A new statement controlling these cosets, with the needed color alignment and uniform mass, remains unpaid.

**Shared-pivot terms and Prediction.** For (x+y)z, choosing xz as monomial anchor leaves yz, which also depends on the latest pivot. The own-pair exposure in §08 freezes q_e while varying the anchor tail using A∩T=∅, and requires adding sets to precede the pivot. This shared-pivot term is outside that contract. Independently, §02 Prediction counts bounded multiplicative masks and additive linear forms in independent block variables. Expanding read-once expressions and declaring their monomials independent does not preserve the algebraic relations. No generalized prediction/conditional counting estimate was established.

All three lifting attempts preserve the original full question; their unresolved obligations are not replaced by a subclass. No result is nominated from family 164.
