# Independent r372 review: 381265 and 331096

Credit **0**. Campaign **52/60 unchanged**, beyond 39 prior. Root has not adopted either author's recommendation. This report supplies an independent ordinary review and an exclusion recommendation for root adjudication; it neither accepts a result nor authorizes Pi. No worldwide priority or formal verification is claimed.

## Decisions and separate gates

| Gate | 381265 | 331096 |
|---|---|---|
| Statement/source fidelity | PASS in the source's finite directed-graph scope, all selected subsets | PASS for the intended annihilator equality; raw typesetting and unrestricted vertex notation defective |
| Ordinary mathematics | PASS: full integral and rational module-dimension proof below | PASS: refutation, strengthened below to two genuine vertices |
| Final/version | Wu's actual 2017 journal body checked at the relevant statements/proofs; broader correction clearance HOLD | Actual Alvir v1 checked; final publication/corrections HOLD |
| Exact earlier resolution and registry priority | HOLD; no authenticated exact earlier resolution | HOLD; 2011 example authenticated, explicit earlier refutation unestablished |
| Novelty | No new-to-literature claim; added argument distinguished from printed theorem | No new-to-literature claim; old ring is not itself a printed refutation |
| Campaign significance | Recommend complete routine source/classical adaptation exclusion, for the reasons below | Recommend complete earlier-example adaptation exclusion, after paying minimality and interior-class bridges |
| Formal endpoint/replay | NOT RUN | NOT RUN |
| Pi | DORMANT; do not dispatch for campaign credit | DORMANT; do not dispatch for campaign credit |
| Acceptance | NOT ACCEPTED; root adjudicates | NOT ACCEPTED; root adjudicates |

The proof of a previously labelled conjecture is not automatically significant. Conversely, neither old ingredients nor brevity would establish a routine exclusion. The recommendations here depend on the explicit reductions, not on either heuristic. Unread generic registry directories remain coverage limits, not specific mathematical objections. No qualified candidate is recommended for execution in this review.

## 381265: exact target and actual source dependencies

The frozen raw record asks for

`K-dim_(Q[E]) H0^Q(G) = K-dim_(Z[E]) H0(G) - 1`

for every directed graph G and selected subset E of E(G). Wu's introduction explicitly defines finite vertex and edge sets, allows loops and multiple edges, and excludes isolated vertices for convenience. The raw record omits that convention. Fidelity PASS means all graphs in this sourced definition, not an unmentioned infinite-graph theory. Adding isolated vertices contributes no incidence relations to H0; the algebraic endpoint also extends to those finite graphs. The edgeless case is treated algebraically below, rather than invoking projective space of dimension -1.

Read source: Wu arXiv:1508.07337v4, dated 29 March 2017, frozen sources/wu.txt. Also independently obtained and read the relevant actual journal HTML: [Journal of Algebraic Combinatorics 46 (2017), 403–444](https://link.springer.com/article/10.1007/s10801-017-0757-3), published 5 May 2017, accepted 10 April 2017, received 5 February 2016. Its Conjecture 1.22 is still the literal equality. The surrounding statements agree at the reviewed passages. This closes the specific unread-final-body objection for these passages, not all subsequent-correction or citing-literature coverage.

Printed dependencies, with their actual limits:

* Definition 1.1: B=Z[x_e : e in E(G)], incidence ideal I generated at each vertex by differences of elementary symmetric polynomials in outgoing and incoming edge variables, up to the larger degree.
* Definition 1.9: module dimension is dim(R/ann_R M), even without finite generation over R. This definition matters here.
* Lemma 2.5: complex projective incidence sets of disassemblies are linear subspaces. Its proof gives equations x=0 on path edges and x=y along each disassembled directed cycle.
* Lemma 2.6: equal elementary symmetric functions of two **complex-number** lists imply a permutation matching the lists. It is stated as a consequence of Vieta, not as an all-ring theorem.
* Lemma 2.7: P(G) is the union of P(D) over disassemblies **as complex projective sets**. Its proof pads the incoming and outgoing lists by zero and matches them separately at each vertex. It does not print an integral radical decomposition.
* Lemma 3.7(1),(4): H0=B/I and for any subring R of B, ann_R H0=I∩R. The proof explicitly supplies this contraction and module-dimension bridge.
* Lemma 4.3: for a commutative Noetherian ring with 1, adjoining one polynomial variable raises Krull dimension by 1; in particular Z[t_1,...,t_r] has dimension r+1 and a polynomial ring over a field has dimension r.
* Lemma 4.6: for homogeneous I⊆(x_1,...,x_n) in Z[x_1,...,x_n], dimensions satisfy dim R_Z≥dim R_Q+1. The proof compares heights at the homogeneous primes using localization and then appends the Z direction. Corollary 4.7 applies this to ann_(Z[E]) H0=I(G)∩Z[E], and prints only the inequality. Remark 4.8 identifies a height condition which would suffice for the conjecture; it does not establish it.

The proof does not assume a finite S-module or use Lemma 4.2's integral-extension conclusion without that hypothesis. Nor does it infer integral equality from equality of complex point sets.

### Full independent bridge, including every changed hypothesis

Let A be Z, let B=A[x_e : e in E(G)], and S=A[x_e : e in E]. At a vertex v put k_v=max(indegree,outdegree). Pad the shorter edge-variable list with zeros to length k_v. Include the unique empty matching when k_v=0. Let Σ be the finite nonempty set of choices of a permutation at every vertex. This is a definition of an indexing set in an ordinary proof; no enumeration was executed.

For σ∈Σ let L_σ be generated by all matched differences. Each difference is x_e-x_f, x_e, -x_f, or 0. The elementary symmetric functions of matched lists agree modulo L_σ, so I⊆L_σ.

Form the equivalence classes of edge symbols under the variable equalities. Mark every class forced to zero by a zero pairing. The homomorphism

`B → Z[t_C : C an unmarked class]`

sends x_e to 0 in a marked class and to t_C otherwise, and fixes integers. It is onto. To prove its kernel is exactly L_σ, choose one representative edge in each unmarked class. Mapping t_C back to that edge class gives an inverse to the induced quotient map: generators in one class become equal and marked generators become zero. Both composites fix all generators. Hence B/L_σ is that polynomial ring. In particular L_σ is a proper prime, with no integer relation hidden in the equalities.

Now let P be **any** prime of B containing I. The domain D=B/P may have characteristic zero or any positive characteristic. At v the incidence equations give equal coefficients in the two monic products

`∏(T-a_i) = ∏(T-b_i)` in D[T].

Substitute T=a_1. A product of differences is zero in a domain, so a_1=b_j for some j. Reorder the second list, cancel the common monic factor T-a_1 in the domain polynomial ring, and induct on list length. The length-zero case is empty. Repeated values and zeros remain repeated indexed entries and cause no exception. No field closure, division by factorials or distinct-root assumption is used. Choose these matchings at the finitely many vertices. They need not be uniquely compatible in advance: all the chosen equalities already hold in D, so together they imply L_σ⊆P for one global tuple σ.

It follows that

`√I = ⋂_(σ∈Σ) L_σ`.

Indeed √I⊆each L_σ because I⊆L_σ and L_σ is prime. Conversely an element of all L_σ belongs to every P⊇I by the preceding construction, hence belongs to √I by the intersection-of-primes characterization. This proves an integral radical identity, including primes over every integer p. It does not prove I itself radical, and does not need to.

For J=I∩S, contraction gives

`√J = (√I)∩S = ⋂_σ K_σ`, with `K_σ=L_σ∩S`.

The radical-contraction equality follows elementwise: s^n belongs to I∩S exactly when s∈S and s^n∈I. Intersections commute with preimage by membership. Restrict the explicit polynomial map B→Z[t_C] to S. Its image is **exactly** Z[t_C : C unmarked and meeting E], since each such t_C is the image of a retained edge variable. Distinct such variables have no polynomial relation. Its kernel is K_σ. Equivalently K_σ is generated in S by retained marked variables and differences of retained variables in the same class; choosing one retained representative per class proves the reverse kernel inclusion. Thus S/K_σ≅Z[t_1,...,t_(r_σ)], where r_σ counts unmarked classes meeting E. Classes with no retained edge supply no variable in this image.

Nilpotents do not alter prime chains: primes over J and √J coincide. For finitely many K_σ, any prime containing their intersection contains one K_σ. To see this, their product lies in the intersection; if none were contained in the prime, choosing one element outside it from each ideal would contradict primality of the product. For any finite strict chain of primes over the intersection choose K_σ in its **bottom** prime. The entire chain is then a strict chain over that same K_σ, bounded by dim(S/K_σ). Conversely every chain over K_σ is a chain over the intersection. Taking suprema proves

`dim(S/J)=max_σ dim(S/K_σ)=1+max_σ r_σ`.

This argument does not splice chains across different components or require equidimensionality.

For rational coefficients one can repeat the domain proof verbatim with Q instead of Z. The matching index set and marked equivalence classes are identical, hence so are all r_σ. The quotients are Q[t_1,...,t_(r_σ)] and dimensions are r_σ. To check the actual rational annihilator directly, put U=Z\{0}. H0^Q≅U^(-1)(B/I), since rationalization of the defining chain complex is exact. Its S_Q-annihilator is I_Q∩S_Q, by testing on 1. Moreover

`I_Q∩S_Q = U^(-1)(I∩S)`.

If s/u∈S_Q maps to I_Q, the membership criterion supplies a nonzero integer v with vs∈I, hence vs∈I∩S. This proves the nontrivial inclusion; the reverse is immediate. This is localization of this explicit quotient/contraction, not an invalid general rule about annihilators of arbitrary non-finitely-generated modules. The same reasoning localizes the coordinate ideals. No flatness of B/I over S is asserted.

Finally ann_S(B/I)=J: an annihilator kills 1+I, so lies in I∩S; any member of I∩S kills the whole quotient by the ideal property. Wu's module-dimension definition therefore yields exactly the required equality from the two maxima. When E=∅, all r_σ=0 and the annihilators in Z and Q are zero, so the dimensions are 1 and 0. When the whole graph has no edges, B=Z,I=0, giving the same endpoint. Isolated vertices add empty lists. A loop occurs once in each appropriate list at its vertex, and parallel edges retain distinct indexed variables. Arbitrary nilpotents or torsion in B/I cannot create additional prime-chain dimension beyond the proven radical decomposition. Nothing in this proof presupposes their absence.

### Significance adjudication and strongest contrary case

**Decision: complete routine source/classical adaptation, not unpaid substantive mathematics.** This is an independent recommendation to root, not a statement that Wu printed the solution. The added steps are the domain version of the printed Vieta matching, quantification over every prime quotient, the integral radical identity, restriction of the coordinate map to S, and the finite-intersection chain argument. The rational localization check is also made explicit here. The actual annihilator bridge is already printed in Lemma 3.7 and Corollary 4.7; polynomial dimensions are printed in Lemma 4.3.

The decisive structural reason for the recommendation is that the source already specifies the complete component family by local padded matchings and already gives its equations using only variable equalities and zeros. Moving that very family through arbitrary prime quotients requires no new characteristic-dependent decomposition or new possible components: factor cancellation proves exactly that none appear. Restriction to an arbitrary selected variable set has the explicit image polynomial ring just proved, so no new elimination theorem about a different class of ideals is required. Once these two bridges are paid, the same finite list of integer class counts computes both sides. This is an extension of the source proof to its unchanged explicit linear component family, followed by the printed dimension formula, rather than an inference from generic standard ingredients.

The strongest contrary case is substantial: Wu explicitly asks this after proving only an inequality; complex geometry generally says nothing about vertical components over Z, and elimination to S can change behavior. This proof adds a useful integral statement not printed in the source and resolves the source question. The counterargument is not dismissed by familiarity. It is answered here by the every-prime matching, integral polynomial quotient and exact contraction proofs. Those are complete and structurally forced by the already printed matching equations. I find no remaining ordinary mathematical lemma requiring new structure. An authenticated explicit prior publication of this exact extension remains unestablished; that separate priority hold neither proves significance nor invalidates this campaign exclusion recommendation.

## 331096: independent refutation with full earlier-example bridge

Read the entire Alvir text, arXiv:1508.02432v1, 10 August 2015. Definition 2 uses an arbitrary index set Λ for a principal-ideal **union**, not an ideal sum. Conjecture 12 takes the simultaneous gcd of a and all n_α, not pairwise gcd representatives. The source does not define a stricter meaning of minimal or impose finiteness. The introduction and Lemmas 1–2 define equality through annihilators; Theorem 5 quantifies over all a even though the graph vertex set excludes zero and regular elements. The raw record has additional malformed typesetting tokens and the same vertex/all-a tension. None is the reason for the refutation below.

The earlier actual journal example is Spiroff–Wickham, [Communications in Algebra 39(7) (2011), 2338–2348](https://doi.org/10.1080/00927872.2010.488675), introduction pp.2338–2339 and Definition 1.1, frozen sources/spiroff-journal.txt. It uses S=Z[X,Y]/(X^3,XY). The journal glyph extraction for Z is imperfect; the frozen arXiv:0801.0086v2 (17 August 2009), introduction, clearly gives Z[X,Y] with the identical ideal and example. The journal's printed equivalence relation is on all ring elements, with [0] and [1] separated from graph vertices. The 2011 online publication date is 20 July 2011; received 31 August 2009, revised 15 March 2010. This precedes Alvir. Alvir explicitly cites this paper as reference [9]. Neither source prints the particular later-conjecture refutation claimed here.

### Minimal union, including infinite-family semantics

Let D=Z[X,Y], I=(X^3,XY). D is a UFD by Gauss's lemma applied twice. Choose one representative of each associate class of nonzero n∈I having no proper nonassociate divisor in I; call the set N. Every nonzero f∈I has a divisor in N: its divisors modulo associates form a finite set, by finite unique factorization, and among those in I choose one with minimum total irreducible multiplicity. Any nonassociate proper divisor has lower multiplicity. Thus I=⋃_(n∈N)(n); 0 lies in every principal ideal and N is nonempty.

If n∈(m) with n,m∈N, then m divides n, so minimality makes them associates and our representatives coincide. Consequently n is not covered by any other member: the union is irredundant, and its principal members are precisely maximal principal ideals contained in I. Indeed any f∈I is divisible by a member n, and any principal ideal properly enlarging (n) inside I would give a proper divisor of n in I. Every principal-union cover must include the principal ideal (n) to cover n. Hence this is not an artificially redundant presentation. It meets the natural irredundancy and divisibility-minimal readings and is canonical at the level of principal ideals. No finite-union or finite-generation substitution is made; finitely generated as an ideal does not mean a finite principal union.

X^3 and XY are among N up to units: their proper divisors are, respectively, 1,X,X^2 and 1,X,Y (up to units), and none belongs to I. Every n∈N is divisible by X. Since gcd(X^3,XY)=X, gcd of the **entire** family N is X up to a unit. This also proves existence for this infinite family: X divides every member, and any common divisor divides these two particular members, hence divides X. Taking a into account is simultaneous throughout.

### Genuine interior refutation, strengthening the author's witness

Take **a=X^2**, rather than relying on the author's a=Y. Then

`gcd({X^2} ∪ N)=X` up to a unit.

In S write x=X+I. Both x and x^2 are nonzero: the monomials X and X^2 are absent from I, whose monomials have either X-degree at least 3 or both positive X- and Y-degree. More explicitly, the Z-module generated by those monomials is exactly (X^3,XY), by expanding polynomial multiples and conversely factoring each listed monomial; independence of polynomial coefficients proves nonmembership. Now x*x^2=0, so both x and x^2 are nonzero zero-divisors and define genuine compressed-graph vertices. But x∈ann(x^2), whereas x∉ann(x) because x^2≠0. Thus

`ann(x^2) ≠ ann(x)` and `[x^2] ≠ [x]`.

This falsifies the conjecture even on its interior vertex domain, with no brackets on a unit. Changing gcd by a unit does not change its annihilator after quotient, since the image of that unit remains invertible. If desired the full colons are (I:X^2)=(X,Y) and (I:X)=(X^2,Y), but the single witness x already proves the necessary difference.

The author's a=Y computation is also correct as an annihilator statement: the simultaneous gcd is 1, y is a nonzero zero-divisor annihilated by nonzero x, and ann(1)=0. The raw graph-only brackets on the right are undefined; that **alone** is not a genuine interior refutation. The a=X^2 repair supplies it. The alternative square ideal can corroborate the general failure, but is not needed, not independently credited, and not used to replace this earlier-example bridge.

### Significance and strongest contrary case

**Decision: complete earlier-example adaptation exclusion recommended.** The printed prior material supplies the exact quotient and annihilator-class semantics; Alvir supplies the attempted arbitrary-union gcd extension and cites that earlier example paper. Added mathematics here is the finite-divisor descent defining the minimal union, its irredundancy, the infinite simultaneous gcd via two forced members, and the interior choice a=X^2. The prior ring's relation x^3=0 with x^2≠0 already displays the two different annihilator behaviors used in that bridge; no new ring construction or classification is required.

The strongest contrary case is that the infinite minimal union is not printed in the journal example and an old ring does not automatically refute a later conjecture. Moreover the author's original witness lands outside the right-hand vertex domain. These objections are real. They are resolved by the full union proof and the two-interior-vertex witness, not by misdescribing the old paper as an explicit refutation. With those bridges paid I find no substantive residual mathematics for this witness. A genuinely different intended finite-only definition of “minimal union” would be a new scope restriction not present in either literal source statement; under that hypothetical reading this witness would need reassessment. The report does not silently impose it.

## Bounded source, correction, citing and current-registry accounting

Three search batches were used, ten queries total. Batch 1: exact Wu title plus journal/conjecture; exact Alvir title plus correction/conjecture; mathlib radical/contraction names. Batch 2: Wu title plus Springer DOI fragment; Wu Conjecture 1.22 proof; Alvir Conjecture 12 gcd counterexample; mathlib radical_inf. Batch 3: exact Wu title/journal pages, Wu correction, Alvir publication. Searches primarily returned arXiv, mirrors, unrelated link-homology work, Wu's own CV and a citing paper entitled “Normed quotient rings.” These are routing leads, not body clearance. The latter's snippet cites Alvir only; it does not identify a specific gcd-refutation theorem and is a citing-literature coverage limit, not a demonstrated subsumer. Unrelated colored-link results have different objects and hypotheses and are not treated as resolutions of this graph problem. Search transport exposes neither a reproducible complete corpus nor HTTP resource telemetry.

Seven explicit direct GET calls were made, each once: mathlib GitHub repository; Wu arXiv abstract; Alvir arXiv abstract; commit-pinned mathlib Ideal/Operations.lean; Wu CV; journal volume/issue; exact Wu journal article. Automatic HTTP redirects are recorded by finalURL, not separate manually issued attempts. If counting network-level redirect hops rather than explicitly requested GET calls, that count is not instrumented and no precise hop-budget claim is made. All seven explicit requests returned 200; the Springer responses retain their cookie-error finalURL but served the article body. No cookie consent, login, token, alternate restricted query, bypass, challenge handling or retry was performed. The server's automatically supplied access text is not an account action by this reviewer. Detailed UTC, finalURL, byte hashes and writer measurements are in http-*.json. No PDF conversion child was run.

Current arXiv pages exactly byte-match the frozen version pages: Wu latest v4 (2017), Alvir v1 (2015). Wu v4 metadata says minor updates/corrections; these are already incorporated in the read v4. Journal relevant bodies have now been read: Conj1.22, Lemmas2.5–2.7/3.7/4.3/4.6, Cor4.7 and graph conventions. No specific unread correction theorem has been identified; subsequent correction/citing coverage is bounded and not cleared worldwide. Alvir final publication remains an unresolved source gate, not an invented specific prior subsumer.

A concrete current public proof-library comparison was performed beyond catalogues. The mathlib repository publicly advertised head **8ae26cc6219b144662f6fa5198925d7c871f3373**. At that immutable head, [Mathlib/RingTheory/Ideal/Operations.lean](https://github.com/leanprover-community/mathlib4/blob/8ae26cc6219b144662f6fa5198925d7c871f3373/Mathlib/RingTheory/Ideal/Operations.lean) was retrieved as text, without Lean/compiler/API execution. In section MulAndRadical the hypotheses are `[CommSemiring R]`. Actual read statements and nearby proofs include:

* `radical_eq_sInf (I)` identifies radical I as the infimum of prime ideals containing I;
* `radical_inf` gives radical(I∩J)=radical(I)∩radical(J);
* `Ideal.IsPrime.inf_le'` says for finite s and ideals f_i, if P is prime then `(inf_(i in s) f_i ≤ P) ↔ ∃i∈s, f_i≤P`.

These precisely apply to ideals in Z[E] and Q[E] in the bridge. They do **not** contain Wu's graph matching/contraction endpoint or Alvir's counterexample. The current head and these exact statement bodies authenticate helper availability only. The file's 2018 copyright and 2026 deprecation notices do not establish introduction dates for individual lemmas; no individual commit chronology or pre-2017 endpoint-priority inference is claimed. Classical statements are also independently proved above where used. Full source endpoint registry clearance remains HOLD.

Frozen author registry heads (OpenAI 4eaee87548250b2682affda7d05d947c05554bae, TauCeti f0b1b42af130787dfc7846cb7c80c2a0de15d569, LeanPool 01db1d7049cf9668bda1e9e106875ee1278b43e6) are sequential author observations, not this review's atomic live snapshot. Their catalogues/import roots cannot clear exact theorem coverage. No absence inference is made from them. No specific unread registry subsumer has been identified. If root later identifies one, that exact comparison must remain HOLD until read. Generic unread directories alone do not veto the ordinary proofs or create a claim of full coverage.

## Inventory, integrity, access and operational limits

The required first command, including the user's trailing dot, ran with actual observed exit 0. It printed complete supplied TASK and all three supplied applicable AGENTS files; bootstrap-receipt.json is preserved. The required second command ran with exit 0 and verified all 80 frozen author inputs, no mismatches. Parent integration was read and is treated solely as verification of 20 raw bindings and 76 artifact hashes, not independent math or root adoption.

Semantically reviewed: the two exact raw JSONL records; their provenance/result entries; DERIVATIONS.md and BRIEF.md; Wu finite-graph conventions, definitions, named statements and proofs listed above; all Alvir text including bibliography; Spiroff journal introduction and Definition1.1; arXiv introduction/definitions as glyph cross-check; targeted version metadata; targeted parent/inventory/access/resource receipts; the mathlib statement contexts; and targeted actual Wu final journal body. Entire-file byte reading is separately logged in receipt-*.json and does not imply whole-body semantic review. Several early combined tool outputs were truncated, and relevant mathematical passages were re-requested in smaller ranges. No semantic clearance is claimed for unshown text, uninspected PDF layouts, other 18 problem bodies, or generic registry trees.

All math/source processing readers installed affinity at most two allowed CPUs, CPU120s and AS6GiB before source reads, with Python -I -B and external timeout140s. Supplied writer has stricter CPU10/AS512MiB. Each helper logs contemporaneous read time, bytes and SHA256; spawned writer jobs have sampled actual child RSS and explicit wait/reaping. Sampling is not continuous descendant/cgroup enforcement. A writer's stdin transfer can precede its RSS sampling; this is a disclosed monitoring gap, not a claim of whole-lifetime sampling. Helpers have no other subprocess descendants. All launched jobs completed and were reaped; no background work remains.

Operational qualification is **LIMITED/HOLD**, not blanket compliance. The initial capped script-inventory read had no persisted contemporaneous per-read receipt; its actual tool exit was 0. Direct script-creation writer invocations use the supplied caps but do not have separate sampled resource records. Two initial inspect.py attempts failed on local import isolation before source reads, actual exits 1; the helper was fixed, then succeeded under -I -B. Receipt writers cannot attest their own future exit inside the receipt they write: tool-observed actual exits are distinguished from exit_intent fields, and exit_intent is never reported as measured true exit. Search-tool internal jobs, statuses and RSS are unavailable. These gaps cannot be retrospectively repaired by invented telemetry. They limit operational acceptance separately from ordinary mathematics.

All artifact writes use this lane's resolved write_lane.py (apart from mandated bootstrap/frozen-verifier receipts). No author/parent/shared index/ledger/dependency/git writes; no /tmp use; no browser/account/message/publication action; no delegation, mathematical enumeration, numerical experiment, CAS, solver, Lean, formal API, Pi dispatch or paper. No protected crown/transitive/bunkbed/tournament bodies were read, hashed, globbed or polled. Only the assigned/frozen paths and explicitly named permitted sources were accessed; no recursive campaign scan or historical-body reopening. Preserve 335255 PARK and 329734's existing root routine exclusion without reopening either.

Deliverables include ID-keyed review.json; actual-hashes.json and its independently recomputed verification; read/resource/HTTP receipts; and frozen-before.json/frozen-after.json. The hash manifest excludes itself, its verification, final audit telemetry and frozen-after.json to avoid circular or future-byte claims. The last frozen check is to be run after all substantive writes. Its actual result, rather than this forward reference, controls the handback. This review leaves priority, bounded coverage, formal, operational and root-acceptance gates distinct from the complete ordinary proofs and significance recommendations.
