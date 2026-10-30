# T250P independent full-proof review (round 1)

Role: independent adversarial proof gate for the frozen T250P target. This is not author assistance, and it gives no contribution verdict. Source theorems at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. Only new deductions were validated. The 13/20 count and the target of 20 were given no weight.

**Verdict: PASS_FULL_T250P.** No required objection. Ten optional clarifications follow. The scope stays exactly as frozen in scope250p.md, with no narrowing.

## 1. Identity work (done before any mathematical use)

- I read verify.py and control-tests.py in full before running them. The verifier has no network access and no write path. It hashes every regular file, rejects symlink ancestry, hardlinks, nonregular entries and nested manifest files, and compares the raw manifest SHA256 with the external argument before calling `json.loads`. control-tests.py creates scratch space inside its own root, so I ran it only on a copy in /var/tmp.
- The five external anchors match the frozen bytes exactly: manifest.json `90c944f1…d821d`, verify.py `f7e05e5f…4d89`, candidate250p.md `92f999bd…4047`, scope250p.md `79fd4364…af72b`, source-and-credit.md `5d5eb86d…cb46520`. The full values are listed in identity-checks.json.
- sources/preprints-tree.json has SHA256 `eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b`, 13223 entries and `truncated: false`, as anchored.
- I compared the actual bytes on disk under private/preprints/ directly against that canonical tree, not against the packet's copied inventory. The three selected families contain 33 canonical blobs: 30 non-PDF blobs and 3 paper.pdf files. All 30 non-PDF blobs are present, with no missing or extra file, and every git-blob SHA1 matches. The 3 PDFs were not retrieved, as the packet discloses. The packet's source-family-inventory.json lists only the 33 blobs and omits the 8 canonical directory (type "tree") entries; all its blob SHAs agree with the canonical tree.
- On the frozen packet in place, `python3 -B verify.py 90c944f1…d821d` returned PASS (62 files, 12 directories, 30 source blobs). I ran it read-only. Nothing was resealed.
- On the copy /var/tmp/t250p-proof-r1-rLoGzx/packet: the correct anchor passed, an all-zero anchor failed with "external manifest anchor mismatch", and control-tests.py passed all 13 cases. The canonical and unchanged_copy cases accepted. The payload, missing, extra_file, extra_empty_directory, root_symlink, ancestor_symlink, hardlink, fifo, nested_manifest, self_reseal and wrong_anchor cases all rejected. diagnostics.py reproduced diagnostics.json exactly. After the controls, the copy verified again. These checks certify bytes only, not mathematics.

## 2. Exact reading and search limits

- AGENTS.md and sources/upstream.json: full.
- frontier/NEW-TEN-2026-10-14.md: lines 1140–1177, plus a regex search for `T250|250P|T253F|E89|I89`. The only hit outside that range was line 1108, which concerns T197H. TWENTY-FINDINGS.md was not consulted.
- Author packet, read in full: candidate250p.md, scope250p.md, README.md, checkpoint.md, formal-interfaces.md, decorated-evaluator-work.md, verify.py, control-tests.py, diagnostics.json. Viewed only through terminal output that truncated its middle: reading-limits.md, source-and-credit.md, affine-and-simple-work.md (sections 1 to the start of 3), diagnostics.py (its beginning and its brick/budget/main parts), and the two provenance JSONs (author-interface-check, companion-comparison), which appeared only as a truncated head. baseline-inventory.json, controls.json, context-receipts.json, primary-retrieval.json (its head was read), source250-receipts.json (its head was read) and source-family-inventory.json (its head was read, then parsed programmatically) were not read as prose.
- Finite-envelope source (Finite-algebraic-envelopes…/build): introduction.tex, reduction.tex, algebra.tex, bootstrap.tex, compiler.tex, affine.tex and action.tex were read in full. kernel.tex lines 1–40 (the Theorem kernel statement) were read; the rest of kernel.tex was not. paper.tex, README.md and references.bib were not read.
- The F-infinity companion and the universal F-infinity preprint were not read by me.
- Primary text files: belk-zaremsky.txt lines 104–122 (the brick, canonical-homeomorphism and twist definitions, including τ_γ(κ)(s)=κ(γ⁻¹s)) and lines 150–290 (including Theorem 3.4, with long lines truncated by the terminal). zaremsky-finite.txt lines 30–70 (the type-(A) definition, Theorem A and Corollary B, with long lines truncated). Olshanskii, Darbinyan–Steenbock and Wächter–Weiß were not read.
- I did not read the t250p-parent receipts or any parallel review directory. I wrote no file outside t250p-proof-r1/ apart from the /var/tmp scratch space.

## 3. Re-derivations by item

**(1) K normalization with protected sectors.** In the quiver, only ω enters O and only α leaves it. So a semantic c(h)=raw(f(h)) is a complete sector bounded by ωα cuts or by the ends of the word, or else the word is a nonpath and evaluates to Ω. Every preprocessing step of N_η is local to a sector, and a full raw sector is already a fixed point. The step that slides Q to its leftmost gap does nothing, because Q follows α directly. Only reverse merges (unmerges) occur. Native preprocessing on the decorated word is therefore exactly the source preprocessing on the expanded word.

The run step replaces maximal runs of t≥2 full raw sectors by raw(f(u₁⋯u_t)). Writing f(h_i) for a semantic payload, f(x f(h) y)=f(x h y) gives the semantic atom c(h₁⋯h_t). A singleton is left literal. Hence the native raw(w) singleton is not c([w]). The candidate correctly keeps it literal. c(h) equals raw(w) exactly when f(h)=w, that is, when w is H-irreducible and [w]=[h].

Literal K outputs are equal exactly when their ωα-sector sequences agree sector by sector. A native full raw sector in the output must be a singleton, and a native sector that is not raw can never equal a semantic one. The comparison is therefore exact.

Weak-component search: the internal graph has outdegree at most 1 on every sector (stipulated), and its vertex set has size at most (k+1)hc^k for fixed bases and boundary flags. Two vertices lie in the same weak component exactly when their forward orbits meet. Checking this needs two counters of O(k) bits and two configurations, and it covers malformed tags and missing boundaries. Workspace cells count in k and carry weight 1, so zero grade does not escape the bound. Finding an entry, finding a q_ok terminal, and finding the lexicographic minimum are each done by enumerating configurations in order. No component is stored.

**(2) H tokens.** A nonempty canonical code is a sequence of complete blocks, each starting with its b letter. No b occurs inside a block, and the T and G alphabets are disjoint. A valid block cannot straddle an atom boundary: a block starting before an atom would contain the atom's initial b, and the atom ends at the end of a block. Unused blocks, meaning b followed by D−1 a/c letters that encode no letter of Y or Z, are native garbage.

After step 2 the state has three invariants: no native valid block, no two adjacent atoms of the same type, and no identity atom. With these, the maximal valid runs of the expansion are exactly the atoms. Tokenization is unique, and static normal forms are canonical. Canonicalizing a maximal run canonicalizes every subrun, because a shortlex-smaller subrun of the same class would give a shortlex-smaller whole. A zero subrun forces the whole run to zero, and absorption then gives ζ.

When an identity atom disappears, newly adjacent native fragments can complete a block. The loop reparses, which covers this. Atoms contain no d, l, r, h, z or ζ, so no selector is hidden inside one. A selector occurrence starts and ends on native markers and consumes whole atoms. Its body's code runs are maximal in the whole word and hence canonical. Since tuple members are irreducible, literal equality reduces to equality of native fragments plus equality of T or G values. Every symbolic step is an H-equality realized by source reductions. At termination the expansion has no redex, so global confluence (Lemma bootstrap: stability plus confluence on every ball) identifies the result with f.

**(3) Literal irreducibility.** The checks are as follows. ζ alone is irreducible. A word longer than one letter that contains ζ is reducible. The empty word is irreducible, since no rule has an empty left side. For each maximal T run C(v): the run is reducible if N(v_K)=Ω. Otherwise it is reducible exactly when some v′ <_shortlex v has the same tested class. This takes one enumeration counter and K calls on native words of length at most |v|. G runs use the Ĝ decider in the same way.

Selector occurrences: the j with a given marker length N is unique, because N_j is strictly increasing. Check the literal body against the members of tuple j, then test eligibility(j). Eligibility(j) tests each member against the static rules and the earlier selected rules. Later selectors are longer than any member and cannot occur in one, so this restricted test agrees with the source's decision at bound n (stability).

**(4) Strict weight.** I checked every call. K c/c→H: −8. K c/raw(w)→H: −7, and the irreducibility call has weight |w|. κ zero or identity →K: −7 or more. Final κ/κ→K: −16. Selector match →K: the child weight is at most W(k)+2N_j/D, below the parent's 8+W(k)+2N_j+2. Eligibility: 2N_j+1 against at least 2N_j+2 marker letters, with children of length below N_j. Literal irreducibility: K calls of weight at most 4L/D<L (zero tests at most 2L/D+1<L, since every run has L≥D), and eligibility calls with 2N_j+1<L.

Normalization never increases weight. Parsing costs 8+2r≤Dr for D≥10. Combining saves 8. Run collapse saves 3t−4≥2. Unmerge preserves weight (4=4), trimming and cleanup decrease it, and component moves preserve the bases. No opaque argument is duplicated, and no frame retains a growing word. Stack depth is at most W, and each frame uses poly(W) space.

**(5) Workspace.** The minimal N_j satisfy N_j≥2N_{j−1}+3, so every relevant j is O(log W), and capped arithmetic stops once N_j exceeds the native budget. Tuple j is found by enumerating encodings of length O(j). The candidate's O(j) bound is valid, though O(log j) also holds. Component searches use O(k) bits.

**(6) Ĝ, P and φ.** A product of pairs, a forward pinch (a,b)↦(1,a) and a reverse pinch (a,b)↦(b,b) each keep the sum of max(|a|,|b|) at most n, and every G query has length at most 2n. P bit lengths are covered in O1 below. From algebra.tex, φ=i∘j with j(b)=ρ(b⊗(e₀−e₁)) and i(h)=c_h−c_ζ for h≠ζ. Over F₂ this gives φ(b)=cκ(b,e₀)+cκ(b,e₁), and both terms equal c(ζ) when b=Ω. By induction, F^r(g)=I+ψ^r(g−I) (affine.tex, eq. matrix-transition), with ψ nonunital, for example ψ(y⊗1)=φ(y)⊗p^op.

**(7) Stage alignment and terms.** The mapping-torus lemma gives t^k q t^{−k}=α^k[q,0]=[Θ^{J−k}q,J], including k<0 through β, with 0≤J−k≤2n. Expanding Σ_i(g₁⋯g_{i−1})v_i and the matrix product into subset monomials gives at most n factors, each a φ-branch of size O(n). That makes O(n²) per term, and a term is indexed by O(n²) bits. The tensor order is (a,b)(c,d)=(ac,db), acting as m↦a m b. Parity counting over F₂ uses two counters and one decorated-equality call, with no dictionary. Equality at stage J is exact because φ and F are injective.

**(8) Bricks.** Using BZ's convention τ_γ(κ)(s)=κ(γ⁻¹s), I re-derived the composition directly. The formulas a′(s)=a(s)·(e(gs)∖b(gs)), d′(u)=d(u)·(e(h⁻¹u)∖c(h⁻¹u)) and twist hg are correct. |a′|≤|a|+|c| and |d′|≤|d|+|b|, and labels are Γ words of length O(n) applied to points of P. On a nonempty brick, the branch is the identity exactly when g=1 and a=b, by independent tails and faithfulness. Consistent itineraries partition C^X.

**(9) Contracts.** Γ is finitely presented, embeds G (finite and trivial G included, with Ĝ infinite cyclic in the trivial case), and acts on the countable X faithfully and two-transitively with finitely generated stabilizers. Theorem kernel is stipulated. Zaremsky's Theorem A (type (A) ⇔ SV_G finitely presented) and BZ Theorem 3.4 (SV_G simple) were read in the primary text. ι_∅ is injective because the action is faithful, and S is nontrivial. No arithmetic on an uncontrolled Steinberg kernel or on arbitrary compressed words is used: only the post-kernel limit description and the specific term family.

## 4. Required objections

None.

## 5. Optional clarifications (non-blocking; I supplied each argument above or below)

- O1. Give explicit bit lengths for P. A word of length ℓ has slope 2^m with |m|≤ℓ. Its intercept and threshold are dyadic with O(ℓ) bits, because the threshold is a maximum of preimages (θ−b_i)/2^{m_i} of 0 or 1 under prefix maps.
- O2. State explicitly that the matrix test sums over nonempty ordered subsets, with I subtracted, and give the translation formula Σ_i(g₁⋯g_{i−1})v_i.
- O3. Fix the Γ alphabet as {p_a, x_{ab}(f) for f∈F, t^{±1}} and note that it generates Γ. In characteristic 2, p_a and x_{ab}(f) are involutions.
- O4. State that the marker length N determines j uniquely, and that eligibility(j) is called only after a literal or semantic body match. The weight bound holds in either order.
- O5. State the post-step-2 invariants and the treatment of unused blocks (see (2)) as a lemma.
- O6. In the coordinate interface, write out the stage alignment, including x's base stage, the t-exponent of g, and β at negative stages.
- O7. Keep the label lists free of duplicates through equality tests, and make the coincident-coordinate concatenation explicit in d′.
- O8. Cite BZ's τ convention explicitly next to the a′ and d′ formulas.
- O9. The tuple encoding length is O(log j). O(j) is true but loose.
- O10. Reading-limit wording: the K-weight sentence "source grade bound at most twice native input length" is unused and could be dropped.

## 6. Disposition

PASS_FULL_T250P at the unchanged frozen scope. Every quantifier is covered: arbitrary finitely generated G with a deterministic polynomial-space word problem, including finite, trivial and non-finitely-presented G. S is a nontrivial, finitely presented, simple group (SV_Γ). The generators embed via finite words. S's word problem is in deterministic polynomial space, with a polynomial that depends on the fixed G, alphabet and decider. No uniformity, F-infinity, torsion, distortion, conjugacy, membership or compressed-word claim is made, and none is needed. Numerical diagnostics certify no mathematics. This verdict is not a contribution or substantiality judgment.
