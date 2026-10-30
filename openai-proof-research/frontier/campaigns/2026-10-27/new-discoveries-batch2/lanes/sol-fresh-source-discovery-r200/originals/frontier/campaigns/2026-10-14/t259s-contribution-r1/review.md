# T259S independent contribution/eligibility review, round 1

Reviewer-owned original prose, CC BY 4.0. This is an independent contribution and eligibility gate. It does not assist the author, read or rely on the parallel proof review, change counts, stage, commit or upload. The parent alone adopts.

## Verdict

**TECHNICAL** for the entire unchanged frozen T259S theorem (all four items, as one statement). Eligible as to scope and chronology; not a duplicate of any exact statement I read; not blocked.

For this gate the full candidate proof is assumed correct. I do not adopt it. The campaign count (13/20, target 20) gave no favourable presumption. No narrower statement is proposed for credit.

The reasons, in one paragraph: the source's own height actions Y_M already have spectral gap, so "two essentially free spectral-gap actions of different costs" follows from the pinned source plus classical representation theory (§2.1). What T259S adds at theorem level is (i) weak mixing of the low-cost action, (ii) cost exactly one rather than at most 1+99/M, and (iii) an explicit gap constant on a fixed pair of generators. All three are obtained by replacing the source's amenable height factor with the Bernoulli shift of a nonamenable quotient. That replacement runs the source's own row-propagation proof verbatim when the quotient is taken to be a free lift of the source height (§2.2). The candidate's "exactly one exceptional row coordinate" is a valid variant of this choice, not a load-bearing new construction. The remaining ingredients are credited source operations (marker graphing, row recovery, cost lower bounds) and classical facts (Bernoulli tensor decomposition, Kesten's 2√3 bound, product weak mixing).

## 1. Frozen object and identity checks

Frozen author packet `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r30/`:

| File | SHA256 (recomputed, matches brief) |
|---|---|
| manifest.json | ff6bd1361506423bf135661e6d930e3635700f14db2de9471548afafc730454d |
| verify.py | 245d3b949fa26a6ae42d214cef89c59a0d425ec8d366c746f69122e9b671d54d |
| candidate-259.md | ee450dee9bd78fb4592313b9b30ac06dd41270019c59da318681423484912491 |
| scope-259.md | 50d98b466935720cfbf9d8f9764f7d8ad8a837a2e58480c7c6b7e44f5ea4f99d |
| sources/preprints-tree.json | eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b (`truncated: false`, 13,223 entries) |

The scope file is byte-identical to the frozen scope quoted in the brief. I inspected `verify.py`, `controls.py` and `diagnostics.py` before running them. `verify.py` is read-only, so I ran it on the original. Controls and diagnostics ran only on an owned disposable copy. Results are in `validation.json`:

* Original packet, correct anchors plus `--source-tree` on the canonical tree: PASS, 26 public and 59 private payloads, 49 authenticated source blobs. A wrong manifest anchor is rejected.
* Copy: diagnostics output equals `diagnostic-results.json` exactly. All 18 copied controls pass (positive, public-only, wrong anchors, edits, deletions, extras, nested manifest, root/ancestor symlink, hardlink, FIFO, self-reseal).
* Actual source changes on copies: a one-byte-appended `group-actions.tex` with a resealed manifest passes the inventory-only check but fails `source identity` with the tree. An altered tree and a `truncated:true` tree are rejected (`source tree identity mismatch`).
* Independent comparison, not using the author's receipts: I computed the Git blob SHA1 of every copied file under `private/preprints/` against the canonical tree. All 49 match, and none is missing or extra. The family259 directory has 14 tree blobs: 13 non-PDF, all present and matching, and the PDF `unequal-costs-rank-100-amalgam.pdf`, not retrieved. It is the only tree directory matching "fixed price". My verifier repeats this comparison directly from the tree (`--author-packet`).

None of this proves mathematics.

## 2. Decisive comparisons (reviewer deductions)

### 2.1 The source Y_M already gives different costs among spectral-gap actions

Source: `group-actions.tex` Lemma `actions:height` and Proposition `actions:low`, and `introduction.tex` Theorem `intro:main`. For M>100, Y_M=X×Z/MZ with (x,r)g=(xg,r+χ(g)) is free and p.m.p., with Cost(Y_M) ≤ 1+99/M. Here χ(a)=1, χ(b_i)=χ(t)=0, and X is the free part of the Γ-Bernoulli shift. The project's I82 §8 had already recorded that Y_M is ergodic. Spectral gap also holds, by the following argument.

* L²₀(Y_M) = (L²₀(X)⊗L²(Z/M)) ⊕ (1⊗L²₀(Z/M)) as Γ-representations.
* The candidate's §7 tensor-label argument, run with Γ in place of H, shows that L²₀(X) is a Hilbert sum of the representations ℓ²(Γ/K_ℓ), where K_ℓ is the stabilizer of a nonempty finite label. Each K_ℓ is finite, since it permutes a finite nonempty support. Each ℓ²(Γ/K_ℓ) is the subrepresentation of λ_Γ fixed by right translation by K_ℓ. (Γ is in fact torsion-free by the classical torsion theorem for amalgams, which makes every K_ℓ trivial, but this is not needed.) Fell absorption gives λ_Γ⊗π ≅ λ_Γ^{dim π}, so the first summand is a subrepresentation of a multiple of λ_Γ. Γ contains the free group A, so it is nonamenable. By Kesten/Hulanicki, no subrepresentation of a multiple of λ_Γ has almost invariant vectors for the finite generating set {a,b_i,t}.
* The second summand is (M−1)-dimensional. U_a acts on the k-th character (k≠0) by e^{2πik/M}, so ||U_a f−f|| ≥ 2sin(π/M)||f|| on it.
* A direct sum of two representations without almost invariant vectors has none. Hence Y_M has spectral gap and is strongly ergodic, for every M>100.

Thus, for any integer M>max{100,99/η}, the pair X, Y_M already consists of two essentially free, ergodic, spectral-gap, strongly ergodic p.m.p. actions of one explicit finitely presented group with different costs. X's spectral gap is classical. Hutchcroft–Pete v2's closing remark attributes it to Losert–Rindler via Schmidt, which I read in the retained primary HTML text. What Y_M lacks is weak mixing (the characters of Z/M are eigenfunctions) and exact cost one. These two items, plus the explicit constant 4−2√3 on (w,b₁), are the whole theorem-level residual of T259S.

### 2.2 The residual is a mechanical lift of the source height

The elements a,u₁,…,u₉₉ form a free basis of A, as recorded in the candidate's §2. The same change of basis is the source's finite-model encoding x_v x_{vu₁}⋯x_{vu₉₉}. Hence any values on a,u₁,…,u₉₉ define a homomorphism, and q(t)=1 extends it to Γ. Take

    q₂(a)=d,  q₂(u_i)=c^i,  so q₂(b_i)=d⁻¹c (all i),  q₂(w)=c⁹⁹d.

With π:F(c,d)→Z, c,d↦1, one has π∘q₂=χ. So q₂ is a lift of the source height through a free group (checked word by word in `routine-lift-check.py`).

On Y₂=X×[0,1]^F with this quotient, the source proof of `actions:low` applies verbatim. "Height k" becomes the translate Ec^k of a marker E={z(1)<ρ}∪(null complement of ⋃_{n≥0}{z(c⁻ⁿ)<ρ}), which is the source's own `actions:small-marker` N_p construction transposed from t to c. The 99 initial height fibres become E,Ec,…,Ec⁹⁸, of total cost 99ρ. The propagation step is the same calculation: for v with coordinate in Ec^{k+99}, the a-sources y u_{i−1} of y=vu₉₉⁻¹ have coordinates in Ec^{k+i−1}, i=1,…,99, and yw=va. Coverage uses ⋃_{n≥0}Ec^n=Z, exactly as in candidate (3). The resulting graphing generates the full relation with cost 1+100p+99ρ, and `compression:cost-one` gives cost exactly one.

The same spectral and mixing arguments then apply:
* q₂(w)=c⁹⁹d and q₂(b₁)=d⁻¹c do not commute, so they generate a free group of rank two. Since rank-two free groups are Hopfian, q₂|H is injective on H=⟨w,b₁⟩.
* Y₂|H is therefore H-Bernoulli, and the candidate's §7 argument yields exactly inequality (1).
* Weak mixing follows as in the candidate's §8.

Items 1–4 of the scope thus follow, with q₂ in place of q, from the source window argument with no new combinatorics. The candidate's q makes 99 of the 100 row sources share one coordinate and recovers one interior edge (D→Dc). That costs one marker instead of 99 and reverses the bookkeeping, but it plays the same role. The "exactly one exceptional row coordinate" is therefore a design variant, not an unpaid construction.

Why a nonamenable quotient at all: for Y=X×Z with Z a Γ-action, the decomposition above shows that Y has spectral gap if and only if Z has none of its own almost invariant vectors. A Bernoulli factor through an amenable image (the r2 profinite height, or a Z-Bernoulli via χ) has almost invariant vectors. Choosing a Bernoulli factor of a nonamenable image is the standard remedy. Its only interaction with cost is the propagation check above, which the free basis makes automatic.

### 2.3 Operation-level credit ledger

The full ledger, with sources and status, is in `credit-ledger.json`. Summary:

| Operation | Antecedent (actually read) | Status |
|---|---|---|
| Γ, embeddings, free basis of J, infinite t, finite generation | source `group-actions.tex` `actions:normal-form` | paid |
| Finite presentation (2) | immediate; recorded in parent r2 screen | paid, no credit |
| Bernoulli free p.m.p., conull restriction | source `group-actions.tex` §2 | paid |
| t-marker C_p and B-graphing, cost 1+100p | source `actions:small-marker`; Gaboriau 2000 Prop. VI.23 | paid |
| Row recovery of an a-edge from w and B-edges | source `actions:low` | paid |
| Cost ≥ 1 for infinite classes | source `compression:cost-one` | paid |
| Cost(X) ≥ 1+η | source `intro:main`, `conclusion.tex` | paid (stipulated) |
| Cost exactly 1 via small upper bounds and infinite factor | parent r2 screen (profinite height) | technical antecedent |
| Ergodic actions of different costs (X, Y_M) | I82 §8 | technical antecedent |
| Spectral gap/strong ergodicity of X and of Y_M | classical (Losert–Rindler/Schmidt per Hutchcroft–Pete; Kesten; Fell) plus §2.1 above | classical, no credit |
| Bernoulli tensor basis, free label stabilizers, 2√3 tree bound | classical; proved in candidate §7 | no credit (candidate concurs) |
| Product of weakly mixing actions weakly mixing; H-Bernoulli mixing | classical | no credit |
| Free basis a,u_i lets q be prescribed freely | source definitions of u_i; source D_V encoding | routine |
| Nonamenable Bernoulli quotient factor carrying the row propagation | §2.2: free lift q₂ of χ runs the source proof verbatim | **residual, technical** |
| One exceptional interior row edge (D→Dc) | variant of the source window | technical variant |

## 3. Theorem-level distinction, residual and correspondence

* **Distinction from the source:** the source theorem gives different costs for X and Y_M. By §2.1 the source's own actions already have spectral gap. T259S's distinct content is a weakly mixing low-cost action of cost exactly one, plus the explicit constant 4−2√3 on (w,b₁). The constant is Kesten's value for the rank-two free group, transferred through a Bernoulli restriction.
* **Distinction from project history:** r2 obtains cost one with a non-strongly-ergodic profinite factor and leaves strong ergodicity open. I82 obtains ergodic distinct costs and opens C82 (ergodic cost interpolation). T259S neither proves nor narrows C82, and it does not repeat either technical partial. It upgrades them along a third mechanical route.
* **Exact residual:** choose a homomorphism q:Γ→F₂ with q(t)=1, prescribed on the free basis a,u_i, whose Bernoulli shift supports the source's row propagation from a small marker and restricts to a Bernoulli shift of a free rank-two subgroup. §2.2 shows this follows by direct substitution into the source proof.
* **Prior-operation correspondence:** marker equals source C_p/Gaboriau VI.23; propagation equals source `actions:low`; exact cost equals source `compression:cost-one` with r2's limiting step; gap and mixing are classical; the lower bound is the source theorem.

The significance of a non-fixed-price group, or the spectral-gap wording, does not by itself make the result substantial. Weak mixing of a cost-one strongly ergodic action is a genuine new-to-project statement, but its proof contains no unpaid operation beyond the routine quotient choice.

## 4. Scope and chronology eligibility

The freeze (2026-10-18T06:25:44Z) followed discovery of the informal quotient mechanism, which already included the cost-one and gap conclusions, and preceded the measurable proof and primary comparison. This is fully disclosed. The parent author-side assistance (`t259s-parent/author-side-interface-check.md`, provenance JSON) is disclosed and is not gate evidence. No earlier frozen broader family259 target exists in the history I read. r2 froze nothing, and I82's C82 is a different, unresolved interpolation target that T259S does not narrow. The exclusions (no Γ-mixing for Y, no universal or fixed-price statements) clarify rather than shrink. **Eligible.** The family262 preliminary material in the packet is not a premise and was not assessed.

## 5. Objections

### Required (for any credit statement or manuscript; none changes the verdict)

1. **Incomplete family259 history.** `source-and-credit.md` reports that history search found only "that parent screen and ledger references". It does not cite `frontier/iterations/i82-measured-group-operator-discovery.md` §8 (2026-10-10). That section is a developed family259 analysis: ergodicity of Y_M, the different ergodic costs, failed bridges, and open target C82. It is summarized in `frontier/TEN-FINDINGS.md` (I82 entry) and `frontier/iterations/README.md`. It must be cited as a technical antecedent. T259S stays eligible because it does not narrow C82.
2. **Spectral-gap separation is already available.** Any statement of contribution must say that X and the source's Y_M already form two free spectral-gap (strongly ergodic) actions of different costs (§2.1). The new dynamical upgrade is weak mixing (with exact cost one and the explicit constant), not the first spectral-gap separation.
3. **Overstated residual.** The "nonamenable quotient with exactly one exceptional row coordinate" must not be presented as an unpaid construction. The free lift q₂ of the source height runs the source window argument verbatim (§2.2). The one-exceptional-coordinate choice is a variant.

### Optional

4. Unread comparators that could only move the verdict toward DUPLICATE, not toward SUBSTANTIAL: Kechris, *Global Aspects*, Chapter 10 (cost and weak containment, minimum cost); Tucker-Drob arXiv:1211.6395; Kerr–Pichot and Glasner–Weiss genericity of (strongly) ergodic and weakly mixing actions; the full Abért–Weiss §§3–4; Khezeli, Bevilacqua–Bowen and Slutsky (cited by the source). None is a premise here.
5. The candidate correctly credits §7 and §8 as classical. A manuscript could cite Kesten for the 2√3 bound and Losert–Rindler/Schmidt for the Bernoulli gap rather than present them as internal.

## 6. Limits

See `reading-limits.md`. Bounded search establishes no literature priority, and no exhaustive literature or history coverage is claimed. Checksums, word checks and controls prove no mathematics.
