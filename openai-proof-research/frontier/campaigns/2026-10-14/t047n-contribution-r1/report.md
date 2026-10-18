# T047N independent contribution/eligibility review, round 1

Role: independent CONTRIBUTION/eligibility gate only. Correctness of the frozen T047N proof is ASSUMED solely for classification; this report gives no proof verdict. The parallel proof-review packet (`t047n-proof-r1/`) and the parent's proof-review brief were not read. No nested agents, staging, commits, shared-metadata edits, counts or uploads.

**Verdict: TECHNICAL.**

The full unchanged T047N theorem (if correct) is a technical consequence. Each operation it uses is either paid by source047 with the exponent 2 replaced by n, or is a standard transfer of the credited Ghosh–Gupta/Ghosh–Pal exponent-recovery template. This template runs: Derksen invariant, then recovery of the modification divisor, then comparison of contracted ideals. Its extra inputs are classical localization/LND, affine-modification and extended-Rees-algebra operations. I found no exact literature duplicate in my bounded search. That absence does not support substantiality under the campaign bar. Count stays 13/20; this review adds nothing to it.

## 1. Anchors and identity evidence (identity only; certifies no theorem)

| Object | SHA256 (all recomputed, all match the brief) |
|---|---|
| author `manifest.json` (external anchor) | `c7eec0bc68f9bb04945e92187ac772fe5339de470745cecb04744db17d1d35cd` |
| author `verify.py` (external anchor) | `609d25eb1ac648f93e5d430fbaf8a09daf19555c1283bb86e5f59ba94adcf880` |
| `candidate-047.md` | `8f68f16a99340c9cf3c83c4ae86386fdcfe2f907bf337afd7f303c7ad0910039` |
| `scope-047.md` | `12e3fb5941a068df0380710b8dcef236e313cdc22ed872ad372b3dab5dfcf181` |
| `sources/preprints-tree.json` (truncated=false, 13223 entries) | `eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b` |
| author clarification `clarification.md` | `354d3a2cb4007abbb8711689f4a89a89110ddd1535755632593df8b809cc1eba` |

I read the author verifier fully before executing it. It is read-only: it hashes files, rejects ancestor, root and payload symlinks, hardlinks, nonregular nodes and nested manifests, and checks the exact file and directory inventory.

- Required full invocation on the ORIGINAL frozen packet (private verification, `python3 -I`, `--source-tree sources/preprints-tree.json`) returned PASS: 17 public and 30 private payloads, plus 21 authenticated source blobs. The same invocation with a one-character wrong manifest anchor was rejected with `manifest external anchor mismatch`. `--public-only` was never used on the original.
- Independent Git-blob comparison (`review-checks.py`): I derived the 21 non-PDF blob paths of the source047 family directory and both family049 companion directories directly from the complete tree, not from the author's receipts. I mapped each to its local private copy and computed `sha1("blob <len>\0"+bytes)`. All 21 match the tree SHA-1s, and there are no other non-PDF blobs in those three directories.
- Own copied controls: 23/23 cases behaved as expected, all on disposable copies under `/var/tmp`, which were deleted afterwards. The three positive cases passed: the full tree, the run without a tree, and `--public-only` on a copy with `private/` removed. The other 20 cases were rejected:
  - wrong manifest or verifier anchor;
  - edited candidate (the `ceil`→`floor` substitution was checked to be a real edit), edited scope, or deleted credit file;
  - extra file, extra directory, or nested manifest;
  - hardlink, FIFO, payload symlink, root symlink, or ancestor symlink;
  - edited source047 or companion body together with the tree;
  - truncated tree;
  - self-resealed manifest;
  - edited verifier copy;
  - `--public-only` with `private/` still present;
  - `--public-only` together with `--source-tree`.

  The first attempt at the source047-edit control was a no-op: its target string was absent from the file. That case passed and was flagged. I fixed it with a guarded, real byte edit. Results are in `review-checks-result.json`.
- Author `controls.py` was read and then run only inside a disposable copy: PASS_ALL_COPIED_CONTROLS (18 cases). The author's `diagnostic.py` was also rerun inside the copy; its output is byte-identical to the frozen `diagnostic-result.json`. These finite checks are not proofs.

## 2. Exact scope coverage (classification assumes correctness)

The frozen scope is restated unchanged in candidate §1. For each n≥2 over C, x=s²+u³+pⁿF, H_n=x²F−(1+2sx)J−pⁿJ²−pu, A_n=P/(H_n), X_n=Spec A_n. The claims are:
- X_n is a smooth integral affine fourfold;
- X_n×A¹≅A⁵;
- X_n≄A⁴;
- X_n≄X_m for all n≠m, under arbitrary C-variety isomorphisms;
- DK(A_n)=S_n;
- intrinsic recovery of pS_n;
- the reduced staircase image((pʳA_n)∩S_n)=I^⌈r/n⌉ mod pS_n.

Every clause is addressed at full scope in candidate §§2–7. There is no marked-p, finite-n or conditional substitute, and no moving-polynomial or nonprincipal-center claim. My classification applies to the full conjunction exactly as frozen. Classifying a proper subset would not change the verdict, since each component is itself technical (§3).

## 3. Operation-level ledger

| # | T047N operation | Who pays it | Classification |
|---|---|---|---|
| O1 | Cylinder A_n[w]≅C^[5] (§2) | Modulo p, H_n≡L=x₀²F−(1+2sx₀)J, which is a coordinate after the determinant-one change in (F,J), independent of n. After p is inverted, H_n is a coordinate. So H_n is a residual coordinate over C[p] for every n. One-stability then follows from Dutta–Lahiri Thm 3.4 / El Kahoui–Ouali Thm 1.1, exactly as source047 Introduction states for n=2. The explicit e-certificate is the source's §02 computation with p²→pⁿ. | Exact standard transfer |
| O2 | Integrality, smoothness | Routine UFD/localization; smoothness descends from the cylinder (as in F004's proof) | Routine |
| O3 | Exact graded algebra G_n=R[τ,I/τⁿ] (§3) | Source §03 `deg:graded-injection`, `prop:graded`, cancellation-reduction with weights (−1,0,0,n,n). Same ring R, same ideal I, same smoothness identity. | Parameter adaptation |
| O4 | ker D⊂S_n for every nonzero LND D, hence DK(A_n)⊂S_n and X_n≄A⁴ (§4) | Source `lem:induced-lnd` already holds for EVERY nonzero LND of A, and `prop:extracted-lnd` uses only "a homogeneous LND D₀ on G with a positive-degree homogeneous invariant". Its contrapositive at n=2 is literally DK(A)⊂𝓕₀A=S, and the source itself credits Gupta's Derksen-invariant strategy (§03, Lemma 2.4 / Prop 3.6 of GuptaThreefold). For general n the changes are: pieces τ^(nq−e)V^qR̃, Case 2 forcing j=nq+1, the multiplier τ^(n−1)V^(q+1), ν(E(r))=ν(r)−1−(n−1)m, ν(E(v))=m−1, and (2−n)m−2<0. I re-derived each of these; they are bookkeeping, and the inequality gets easier as n grows. The torsor, normalized lift (its conjugacy proof is n-agnostic: the scaling becomes V↦λⁿV) and cubic rigidity are invoked unchanged. | Parameter adaptation of a paid mechanism |
| O5 | DK(A_n)⊃S_n (§5) | p, x, y, z come from denominator-cleared partials on A[p⁻¹]=C[p^±1,x,y,z]. This is standard localization of LNDs: pᴺ∂ preserves A once it preserves generators, and the invariant multiplier keeps local nilpotence. u comes from pⁿδ₁, where δ₁ is the standard Danielewski-quadric LND (δz=x, δy=2z+1) on xy−z(z+1)−p^(n+1)u. This is the same kind of step as GG Lemma 2.9 and GP Lemma 3.1(i): explicit exponential maps containing the coefficient algebra in DK. | Standard |
| O6 | Intrinsic recovery of V(p) (§6) | The canonical birational morphism Spec A_n→Spec DK(A_n) is the affine modification of S_n along the divisor p=0 with center V(I). Its non-isomorphism locus is the exceptional divisor, with A¹ fibers over the center. This is Kaliman–Zaidenberg affine-modification geometry; the source already names G as such a modification (§03). GG Thm 4.1(ii) and GP Thm 3.2(ii) recover the same divisor by divisibility in B. T047N uses the isomorphism locus because S_n is not a polynomial ring, but this is a standard alternative route, not a new idea. | Standard transfer |
| O7 | Reduced staircase Jbar_r=I^⌈r/n⌉ (§7) | Upper inclusion: for b∈S∖pS with b=pʳa, the source's graded injection [h]_d↦\overline{p^d h}τ^(−d) sends init(a) to b̄τ^(−r), which lies in the degree-r piece of R[τ,Iτ^(−n)], namely I^⌈r/n⌉τ^(−r). For n=2 this is read directly off source `prop:graded` (the source's `red:pieces` already shows the same ceil pattern on G̃). For general n it is the textbook homogeneous-piece computation of an extended Rees algebra. Lower inclusion: products of the lifts pⁿF, pⁿJ. | Standard computation on a paid graded ring |
| O8 | n=max{r: Jbar_r=Jbar_1} via I²≠I (§7) | Nakayama/Krull | Routine |
| O9 | Assembly: abstract A_n≅A_m ⇒ n=m | Precisely the GG Thm 4.1 / GP Thm 3.2 template, which the author credits: DK is intrinsic, the divisor is recovered, contracted ideals are compared, and the exponent follows. The primary theorems do not apply directly, because their DK/ML hypotheses are polynomial subalgebras and fail here. T047N replaces exactly those hypotheses with O5–O7, and each replacement is standard. | Standard transfer of a credited template |
| O10 | Not polynomial S_n (χ_c=2), §8 | Ancillary and unused | Routine |

**No unpaid operation remains.** The unpaid step that would have been needed for substantiality is a genuinely new obstruction or invariant: something not already supplied by (a) source047's per-LND positive-degree-invariant exclusion, (b) the source's exact graded identification, and (c) the GG/GP divisor-recovery and contraction template. T047N contains no such step. The longest new passage (O4 bookkeeping) is a parameter adaptation that the author's own `source-and-credit.md` already calls technical. Under the campaign bar, none of the following establishes substantiality: a new complex family, a nonpolynomial coefficient ring S_n, a two-generator center, a longer proof, or characteristic 0 instead of p.

## 4. Primary-antecedent comparison and the author clarification

I read the actual operative bodies. They are:
- **GG** Thm 4.1 with its full proof, Thms 4.2–4.3, Cor 4.4, Lemma 2.9, Prop 2.10–2.12 and Thm 2.3;
- **GP** Lemma 3.1, Thm 3.2 with its full proof, and Remark 3.3(i)–(iii).

Template: both papers do (i) DK and ML restriction, (ii) recovery of the prime factor of the modification coefficient, and (iii) comparison of contracted ideals xʳA∩B to equate exponents. Both conclude with infinite pairwise nonisomorphic positive-characteristic cancellation families (GG Cor 4.4; GP abstract). T047N's assembly O9 is this template.

The author clarification (formula-level issue): I independently confirm it. Suppose r_i>s_j in the proof of GG Thm 4.1(ii) (and symmetrically r_i<s_j in GP Thm 3.2(iii)). Then the displayed equality (x'_j)^{r_i}A∩B=((x'_j)^{r_i},(x'_j)^{r_i−s_j}G)B omits G^k for k=⌈r_i/s_j⌉≥2. The reason: G^k=(x'_j)^{k s_j}(y')^k·(other factors)^k ∈ (x'_j)^{r_i}A, while x'_j∤G^k because x'_j is prime in the polynomial ring B. So the displayed inclusion in x'_jB is not justified as written. This is a statement about one displayed step, not about the theorems' conclusions. I checked an m=1 repair:
1. Take the filtration with deg x'=−1 and deg y'=s, the admissible-filtration device both papers already use (GG Lemma 3.2; GP Remark 3.3(ii)–(iii)). It gives image((x')ʳA∩B mod x')⊂(ḡ^⌈r/s⌉).
2. F∈xʳA∩B with F∉xB gives f̄∈(ḡ^k).
3. Symmetrically, ḡ∈(f̄).
4. Hence ḡ^(k−1) is a unit. This is impossible: a unit ḡ would make x' a unit in A', which DK(A')=B' excludes.

I did not verify the m>1 repair, where the extra coefficient factors appear.

Consequences for classification:
- The reduced-modulo-the-divisor staircase is the natural repair of the antecedent's step, built from the antecedent's own filtration tools. T047N's O7 is its two-generator analogue on a ring the source already computed. The issue therefore does not create substantiality for T047N, and I retain full strategy credit for GG/GP.
- The model (p³A)∩k[p,t]=(p³,pt,t²) for t=p²Y is exact (monomial pⁱtʲ ↦ p^(i+2j)Yʲ, with membership i+2j≥3). As the clarification states, it does not satisfy the primary DK/ML hypotheses and is not a counterexample to their conclusions.

The Blanc–van Santen comparison concerns the abandoned pre-freeze moving-cubic idea. It does not close or pay anything in the frozen thickness theorem. I did not reread it beyond the author's receipts (see reading-limits).

## 5. Eligibility

- Source: source047, pinned at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and stipulated true. The complete non-PDF family is authenticated against the complete tree. Only the generic lift statement (`prop:linearization`/`prop:homogeneous-lift`) and the unchanged rigidity (`prop:rigidity`, same R̃, v and weights) are invoked as stated. This matches the brief's restriction. The n-version of the homogeneous-lift conjugacy is re-argued in candidate §4, not silently assumed. I spot-checked that the source proof is n-agnostic, but proof soundness belongs to the proof gate.
- F004 (read fully) counts the cancellation-to-cyclic-action consequence. T047N contains no group-action corollary and does not recount F004. Not a duplicate of F004.
- Campaign exclusions: the NEW-TEN ledger, its exclusions section and the post-R034 tail were read (§6 of reading-limits). No prior campaign screen of family047 thickness variation was found. The r39 `history-index.json` match was only seen by search and not read.
- The family049 companions (two directories): I authenticated their bytes but did not semantically read their bodies. I rely on their pinned titles and the author's reading report: noncoordinate and stable-coordinate embeddings, not pairwise nonisomorphism. No T047N step uses them.
- No catalogue manuscript states this family. I did not semantically read the full catalogue.

**Eligible, not DUPLICATE, not BLOCKED. Contribution level: TECHNICAL.**

## 6. Numbered objections

Required. These apply to any adoption or later wording; they are not repairs to the frozen bytes.

1. **R1 (classification).** The residual named in `source-and-credit.md` ("exact intrinsic S_n/divisor/staircase calculation") must be recorded as a technical transfer. DK⊂S_n is the per-LND form of source047's positive-degree-invariant exclusion. DK⊃S_n, divisor recovery and the reduced staircase are standard (O5–O7). No campaign record may describe them as a new mechanism.
2. **R2 (credit precision).** Credit source047 `deg:graded-injection` together with `prop:graded` as already yielding the n=2 reduced staircase, and `lem:induced-lnd` together with `prop:extracted-lnd` as already yielding DK(A₂)⊂S₂. Credit residual-coordinate theory (Dutta–Lahiri Thm 3.4) as giving the cylinder for every n directly, since H_n mod p is n-independent.
3. **R3 (primary-issue wording).** Any record of the GG/GP displayed-contraction issue must say the following:
   - it concerns the displayed identity only;
   - the omitted Gᵏ powers are genuine under their hypotheses in the contradiction branch;
   - an m=1 repair via the papers' own admissible filtration was checked here, and m>1 was not;
   - no theorem-conclusion error or counterexample is asserted;
   - the repair is not T047N's contribution.

Optional:

4. **O1.** Before any external novelty wording, read the bodies of the classical thickness-varying families. Two were seen only at abstract or snippet level: Danielewski surfaces xⁿz=y(y−1) (pairwise nonisomorphic, isomorphic cylinders) and Gupta–Sen, *On double Danielewski surfaces and the Cancellation Problem*, J. Algebra 533 (2019), arXiv:1908.03403 (ML invariant and isomorphism classes of a two-step family). The idea of varying the thickness of an affine modification to get an infinite family with a fixed cylinder is old in spirit.
5. **O2.** Gaifullin–Petrov (arXiv:2607.13593, cited by source047) and arXiv:2501.09613 surfaced in search snippets only. Neither was read. Any "first infinite complex family" phrasing needs those bodies read; T047N currently makes no such claim, correctly.
6. **O3 (for the proof gate, not a verdict).** Confirm that (4.1) for e>0 and the Case 2 extraction with multiplier τ^(n−1)V^(q+1) are exact for every n≥2, and that the source rigidity accepts every nonpositive fiber shift −2(q+1). My re-derivation agreed, but it is not a proof review.

No blocking mathematical issue was found for classification purposes.

## 7. Final verdict

**TECHNICAL** for the full unchanged T047N conjunction. Each operation is paid as follows:
- O1: exact standard transfer by residual-coordinate theory;
- O3/O4: parameter adaptation of source047's graded, torsor, lift and rigidity chain, whose per-LND form already is the DK upper bound;
- O5/O6/O7: standard LND localization, the Danielewski-quadric LND, the affine-modification exceptional locus, and the extended-Rees homogeneous pieces;
- O9: the credited Ghosh–Gupta/Ghosh–Pal exponent-recovery template.

No narrowed variant is proposed. The parent alone decides adoption.
