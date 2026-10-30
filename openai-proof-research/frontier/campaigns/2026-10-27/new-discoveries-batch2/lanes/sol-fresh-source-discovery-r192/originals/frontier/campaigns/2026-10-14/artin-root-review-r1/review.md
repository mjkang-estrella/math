# Independent review round 1: full Artin parabolic root closure R

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party inputs remain private and retain their original rights.

**Mathematical verdict: PASS_FULL_R, relative to the expressly stipulated upstream theorems and the established Digne–Godelle–Michel retraction interface.** Every new deduction needed for the full target checks out. No mathematical repair or scope restriction is required.

**Contribution triage: TECHNICAL.** The proof gives a correct full consequence of the inputs. Its additional operations are an elementary complement construction from an existing twisted product law, followed by the standard parabolic-closure reduction. This assessment is independent of the author's decision not to nominate and of the parent's non-gate assessment. It is not based on proof length. No worldwide novelty certificate, substantial-result acceptance, publication authorization, or count increase is supplied. The campaign remains **4/10**.

## Scope and dependencies

For every finite set S, including the empty set, every symmetric Coxeter matrix with diagonal 1 and off-diagonal labels in {2,3,...} union {infinity}, every X contained in S, every u,g in its Artin group A, and every nonzero integer m, the reviewed assertion is

    g^m in P = u A_X u^{-1}  implies  g in P.                 (R)

The r2 and r11 `original-scope.md` files agree byte for byte. There is no spherical, FC, large-type, dimensional, positivity, connectedness, or ribbon-generation assumption.

The proof uses precisely the following mathematical interfaces.

1. At the stipulated openai/math revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, *Parabolic intersections in Artin groups*, `cor:arbitrary-intersections`: arbitrary intersections of parabolics are parabolic; every subset has a unique smallest parabolic closure PC. The statement includes arbitrary finite and infinite labels and finite S. The containing family is nonempty because it contains A. Its proof in `08_stabilizers.tex` explicitly obtains a finite witness by strict rank descent. Pairwise intersections alone are not substituted for this interface.
2. At the same pin, *Harmonic heights and the Artin K(pi,1) conjecture*, `cor:artin-structural` (i): A is torsion free for every finite S. The statement and its finite-dimensional-classifying-space consequence include the empty case. As instructed, upstream theorem truth is accepted, not re-audited.
3. Digne–Godelle–Michel (DGM), [*Retraction to a parabolic subgroup and applications*, arXiv:2407.07459v2](https://arxiv.org/html/2407.07459v2), Proposition 2.4, Proposition 2.6(1),(7),(8), and Lemma 2.7. These provide a well-defined set retraction rho_I:A -> A_I and the product law below. Definitions 1.2 and 1.14, Lemma 1.1, and Proposition 1.16 identify its word and Coxeter-ribbon interfaces. These statements concern arbitrary Coxeter type and arbitrary signed Artin words.

Write theta:A -> W and Q=A_I. For theta(a) in N_W(W_I), Lemma 2.7 supplies a Coxeter I-ribbon-I w in W_I theta(a) and the induced generator-renaming automorphism alpha_a of Q, with

    rho_I(a b) = rho_I(a) alpha_a(rho_I(b))    for every b in A. (1)

Also rho_I(q)=q for q in Q, and Proposition 2.6(7) gives

    rho_I(q b) = q rho_I(b)                  (q in Q, b in A). (2)

These are established source operations. No global group-retraction claim is made.

## Independent check of the source boundary

The retained original TeX, not merely an extraction or title, states Lemma 2.7 under theta(a) in N_W(W_I), without a spherical or FC condition. The finite-type discussion earlier in the introduction concerns a different proposition about powers of Delta. It does not restrict Section 2 or Lemma 2.7.

Here is a direct check of the possible Coxeter-normalizer pitfall. Let x normalize W_I and let w be the minimum-length element of W_I x. Since w differs from x by left multiplication in W_I, w also normalizes W_I and is I-reduced. For s in I, ws belongs to W_I w. Minimality forbids a length decrease, so w is also reduced-I. DGM Lemma 1.1 applied to w and s says that ws w^{-1} in W_I actually lies in I. Conjugation is injective on the finite set I, so this map is onto I. Equivalently, applying the same reasoning to w^{-1} gives its inverse. Thus the source's I-ribbon-I conclusion maps I onto I, rather than merely into the reflection subgroup W_I.

For s,t in I, simultaneous conjugation preserves the exact order of st. In a Coxeter system that order is m_st, including infinite order when m_st=infinity. Hence the permutation preserves the entire Coxeter matrix. Renaming Artin generators by it and by its inverse preserves every defining finite braid relation and the absence of a relation at infinite labels. The induced alpha_a is a group automorphism, so it is injective and fixes 1.

The DGM proof itself writes theta(a)=v w, lifts w to its simple positive lift a_w, and puts a_1=a a_w^{-1}. Now theta(a_1) lies in W_I. Proposition 2.6(7) applies to a_1, and (8) applies to a_w; (5) gives rho_I(a_w)=1. This yields (1), with b=1 identifying rho_I(a_1)=rho_I(a). I checked this deduction against the original proof. It uses an available Coxeter ribbon and its diagram permutation, not generation of the Artin normalizer by Artin ribbons. Nor does it require the assignment a -> alpha_a to have been established as a homomorphism.

## Independent reconstruction of the entire new deduction

Let N=N_A(Q). For n in N,

    theta(n) W_I theta(n)^{-1} = theta(n Q n^{-1}) = W_I.

Thus (1) applies to every element of N. Define

    K = {k in N : rho_I(k)=1}.

The identity lies in K. If k,l lie in K, then (1) gives rho_I(kl)=1 alpha_k(1)=1; their product also lies in N. If k lies in K, apply (1) to k k^{-1}: 1=alpha_k(rho_I(k^{-1})). Injectivity of alpha_k gives rho_I(k^{-1})=1, and k^{-1} lies in N. Therefore K is a subgroup. This explicitly pays inverse closure; the zero fiber of a general set map is not being called a kernel.

Since rho_I restricts to the identity on Q, K intersects Q trivially. Given n in N, take q=rho_I(n) in Q and k=q^{-1}n. Because Q is contained in N, k lies in N. Equation (2) gives rho_I(k)=q^{-1}rho_I(n)=1. Thus n=qk and N=QK.

Q is normal in N by the definition of a normalizer. Consequently the quotient map N -> N/Q restricts to a homomorphism on K. Its kernel is K intersect Q={1}; it is onto because every n=qk has quotient kQ. Hence

    K is isomorphic to N_A(Q)/Q, and N = Q semidirect K.       (3)

Only Q, not K, must be normal. The argument does not require rho_I to be homomorphic on N, let alone on A. It proves the quotient is isomorphic to an actual subgroup of A. Torsion-freeness of A therefore does imply torsion-freeness of this particular quotient, using (3).

For an arbitrary parabolic Q=u A_I u^{-1}, conjugation by u identifies its normalizer and quotient with those for A_I. In particular u K u^{-1} is a subgroup of A isomorphic to N_A(Q)/Q. Thus the quotient conclusion holds for every parabolic in the original scope.

For any subset E and a in A, conjugation bijects the family of parabolics containing E with those containing a E a^{-1}. It commutes with their intersections. Therefore

    PC(a E a^{-1}) = a PC(E) a^{-1}.                          (4)

Suppose m>0 and g^m lies in P. Put Q=PC({g^m}). The stipulated closure theorem gives a parabolic Q contained in P and containing g^m. Since g centralizes its own power, (4) gives g Q g^{-1}=Q. Thus g lies in N_A(Q), and (gQ)^m=Q. The torsion-free quotient just proved forces gQ=Q, whence g lies in Q and in P. If m<0, the subgroup P contains (g^m)^{-1}=g^{-m}, to which the positive argument applies. This handles all nonzero exponents, including +/-1.

For I empty, rho_I is the constant identity map, K=A and the quotient is A. For I=S, rho_I is the identity map, K={1} and the quotient is trivial. If S is empty, A itself is trivial. PC({1}) is {1} because the trivial parabolic is among its containing parabolics. There is no exceptional trivial, whole, empty, disconnected, or infinite-type case. All conjugators are covered by the conjugation argument. This proves unchanged full R.

The author's final equivalence is also correct: given these retraction and closure inputs, root closure of every parabolic is equivalent to torsion-freeness of A. The forward implication uses the trivial parabolic; the reverse implication is the proof above.

## Objections retained, not silently discharged by a false shortcut

The r11 normalizer-quotient and parabolic-closure reductions remain valid. The additional DGM law supplies the formerly missing quotient embedding. Neither ambient torsion-freeness alone nor asphericity alone would do so.

Same-transport `null:hom` and the negative-total-degree Hom input in `null:injection` still concern one common transport z. Their hypotheses do not extend to arbitrary sums of different transports. The rank-one evaluation cone gives FP_f=[P_s<1> -> P_f], and cancelling evaluation on P_s gives FP_s=P_s<2>[1]. Applying F to the first triangle gives the minimal complex F^2P_f=[P_s<3> -> P_s<1> -> P_f], with token then arrow in cochain placements -2,-1,0. The induced token is nonzero because F preserves the original nonzero arrow class. A map from P_f to the upper layer P_s<3> has bidegree (-2,4), with one length-one class and no adjacent length-zero or length-two space. Its cross h_1 is one. On P_f direct-sum F^2P_f the aggregate middle dimension/outgoing rank are 2/1, not 1/0. This retains the original obstruction. It is not a nontrivial periodic Artin orbit, and this review does not infer that such an orbit exists.

No equivariant null-layer/two-point extension for orbit sums is proved or used. Individual harmonic minima, folding, and additive frame counts do not supply it. The B3 elements st and ts still differ (their S3 images are distinct) although (st)^3=(ts)^3=Delta^2. Root closure does not assert unique roots of arbitrary elements. The Z^2 family {0,2Z x {0},Z^2} still separates intersection/index/torsion-free properties from root closure; its middle subgroup admits no product law giving the complement used here. Proper-parabolic infinite index does not prove parabolicity of a finite extension. No CAT(0) metric or action is inferred. These objections are bypassed by a valid additional source interface, not revoked.

## Independent contribution triage and actionable attribution

The nonroutine operation in this proof route is DGM's arbitrary-type twisted multiplication formula. DGM already prove it, including the passage from a normalizing Coxeter image to the correct ribbon and product formula. Proposition 2.6(7) already supplies left-Q equivariance, and Lemma 2.9 already supplies a canonical zero-retraction representative for every coset. The new complement proof checks closure, inverses and uniqueness using precisely those identities. These are standard elementary subgroup and quotient operations. The final PC step is the conjugation-equivariant closure reduction already isolated in r11. No new periodic-orbit theorem, categorical estimate, normalizer presentation, or relative geometric construction is contributed.

The operation comparison therefore supports TECHNICAL even if the full combined consequence has not appeared verbatim in the literature. The generality of the resulting theorem is real, but comes from the generality of the paid inputs. Shortness itself is not the reason: a short proof introducing a new nonroutine operation could merit a different assessment. Here the identities leave no comparable additional mathematical obstacle unpaid.

The source screen gives the following more precise attribution boundaries.

* In DGM's retained v2 original TeX I found the normalizer product law, not an explicitly stated general normalizer semidirect-product theorem. I searched the full TeX for normalizer/normaliser, split, semidirect/complement terminology and product notation, and read the relevant occurrences and the coset results. This is a bounded negative finding, not a literature-wide absence claim. DGM's law directly supplies the elementary general splitting in (3).
* Explicit normalizer splitting is already stated in primary literature for spherical type. GHLY's retained original body, Theorem 5.6, states Norm_A(A_J) is isomorphic to A_J semidirect R_J and identifies R_J with the quotient, crediting Godelle [14, Proposition 4.4]. The start of Section 5 explicitly imposes spherical type. Godelle's [*Parabolic subgroups of Garside groups II: ribbons*, arXiv:0811.0751v1](https://arxiv.org/html/0811.0751v1), Theorems 1.3 and 4.25(ii), gives the groupoid splitting under its Garside/nu-structure hypotheses, expressly including spherical Artin groups. Its proof uses Garside fractions; those are not a general arbitrary-type premise here. These are actual splitting antecedents, not just similarly titled papers.
* CMV's [large-type paper](https://doi.org/10.1017/S0305004122000342), Section 6, Proposition 37/Lemma 38/Corollary 39, already proves large-type root closure through finite-orbit systolic fixation and rank induction. Corollary 34 gives an explicit rank-one normalizer direct-product description. Neither subclass result is a new result of r2.
* HMS [arXiv:2503.20620v1](https://arxiv.org/html/2503.20620v1), Definition 5.9/Theorem 5.10/Lemma 5.11, records two-dimensional root closure credited to Godelle Corollary 3.8. I read these exact interfaces and their cited reference; I did not independently audit the original Godelle 2007 proof.
* GHLY [primary paper](https://ogarnier.github.io/pub/norm_artin_tits_cone.pdf), Theorem 1.8, constructs a particular arrangement classifying-space model in spherical ambient type; Conjecture 1.10 asks for its extension. The quotient embedding (3) does not identify that space or prove that conjecture. Its arbitrary-type atomic Matsumoto Theorem 1.4 has a different conclusion.
* Heng–Licata–Yacobi [arXiv:2502.20711v1](https://arxiv.org/html/2502.20711v1), Theorem 1.1 and Lemma 2.6/Theorem 2.7, concern finite-type central-power periodicity, the full-twist shift and a stability-space cover. These do not give the general relative parabolic assertion.

**Actionable correction:** no proof correction is required. If retaining an attribution paragraph, add the explicit spherical splitting antecedents GHLY Theorem 5.6 and Godelle Theorem 4.25(ii). Describe the arbitrary-type splitting as an elementary consequence of DGM Lemma 2.7, rather than as a new substantial normalizer mechanism. I do not classify the full arbitrary-type consequence as DUPLICATE: this bounded review did not locate a primary statement already asserting the full combined result under the exact stipulated inputs. That limit does not prevent TECHNICAL triage.

## Actual reading and verification limits

Read in full: applicable repository AGENTS.md; all six required r2 files (`candidate.md`, `original-scope.md`, `source-contracts.md`, `normalizer-checkpoint.md`, `research-notes.md`, `literature-screen.md`); the corresponding r11 candidate/scope/contracts/notes/screen; parent r2 and r11 disposition/verification records; the supplied current brief and reproduced history. Historical source authentication does not mean every historical assignment was performed anew.

Primary bodies read for this review: DGM original TeX lines 84–230, 280–390, 548–596, 610–705, 740–935, and 1940–2040 (definitions, descent, relevant product/ribbon proofs and closure-conjecture context); full-text normalizer/splitting occurrence searches as described above. Pinned parabolic introduction and stabilizer section through the arbitrary-intersection proof, with the exact proof re-read at lines 150–172; pinned K(pi,1) introduction and full consequences section; CAT(0) companion introduction. For the retained categorical objection: parabolic `02_category.tex` lines 195–220 and 360–425, and `05_null.tex` lines 1–230. These support the displayed rank-one reconstruction; no archived checker was run. This is not a fresh audit of all abandoned r2 categorical symmetry claims.

Literature reading: GHLY text pages 1–4, Section 2.3/Lemma 2.8 and Section 5 through Theorem 5.6/Remark 5.7; CMV exact Section 6 root-closure statements and full Proposition 37/Lemma 38 proof, plus Corollary 34 and surrounding normalizer scope; HMS Definition 5.9 through Lemma 5.11 and proof/reference; HLY retained text lines 76–103 and 260–303; Godelle 0811.0751v1 introduction/Theorem 1.3 and Section 4.4/Theorem 4.25, including the proof's Garside-fraction step. No full independent Garside-theory audit or worldwide priority search is claimed. Initial large tool windows were truncated; decisive source statements and proofs were followed by focused reads.

The frozen r2 seal authenticates to `92f9d1b04e4631cb436a58b7aeb46c2444f25d63fff50522ea0a7cc155735003`. I inspected the parent hash-only authenticator before running it. It passed with exactly the declared historical-ledger substitution: 35204 bytes, SHA256 `4ed78e1bf88ff9b7ec0360673424d2c5ee973daafa1aa87b0b07f0fa6283eef8`. The live ledger was never replaced, and I do not claim that the original direct r2 verifier passes the current live context.

Independent hash/Git checks authenticated all 78 pinned blobs against the complete nontruncated preprint catalogue, exact r2 membership (30 files), all 240 external frozen-tree files, and 20 declared fixed context records with that one historical-ledger substitution. The retained DGM archive was opened as data only; its TeX member agrees exactly with the retained original TeX. Its SHA256 is `d32a1051f23b58a99cb3eb1e6fb33f5172e769fa06ac541a4af7a0fd95e18f72`. No frozen child, historical mathematical checker, or third-party code was executed. The newly fetched Godelle HTML is privately retained with its versioned URL and immutable receipt.

`source-records.json` identifies actual read sources, their sizes/hashes, upstream Git identities where applicable, and reading extents. `external-baseline.json` records exact frozen membership and initial context authentication; `inputs-manifest.json` and `outputs-manifest.json` seal the review's exact membership. Mutable parent records and the historical ledger used by this review have owned snapshots. The review verifier binds the frozen source trees and owned snapshots, not the future live ledger or whole parent directories. It is read-only, performs integrity checks only, and certifies no mathematics by computation. No finite search is needed for the universal argument. The detached review seal is reported outside the package in the final response.

All writes are confined to `artin-root-review-r1/`. No nested agents, staging, commits, shared-file edits, external messages, upload, submission, or publication occurred. This independent mathematical PASS retains the correct full theorem as a technical consequence; it does not count or authorize packaging/publication.
