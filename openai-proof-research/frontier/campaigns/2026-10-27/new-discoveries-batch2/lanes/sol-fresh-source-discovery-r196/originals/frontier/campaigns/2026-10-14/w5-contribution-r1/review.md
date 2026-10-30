# W5 independent contribution and eligibility review, round 1

Reviewer output by an independent Claude Opus 5.5 review worker. Author of record for this original report: Myeongjin Kang, no affiliation. Original prose CC BY 4.0; code MIT. This is not a proof review, and it does not audit whether the source is correct. Source theorem truth at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is taken as given.

## Verdict: **TECHNICAL**

The full, unchanged W5 conjunction is eligible. No earlier developed chain was found, and no read source or primary statement already contains it, so it is neither SUBSUMED nor INELIGIBLE. Its one new ingredient is a basepoint-free family of sup-weighted scalar functions for the source's weight. That family comes from a short canonical device applied to the explicit structure the source already supplies. Everything else is classical finite generation plus the standard Hartogs fibre-coefficient embedding. I found no unpaid mechanism beyond this routine combination of source and classical operations. I make no claim about worldwide priority, either for or against.

## 1. Identities reviewed (exact)

| Object | SHA-256 |
|---|---|
| author `manifest.json` (external anchor) | `10665dc832a51bca7651cbb091951b8b3ae3a7442339a64fd3b69e4b9743c606` ✓ |
| `original-scope.md` | `bda045b928a2f5b4ea52b96eb1ae6f3ea17146a575cefd955461994399d19f03` ✓ |
| `candidate.md` | `2fd9649ae04c531eca486848917cbc3dc7ddfffdac9881ff1742594d2060147d` ✓ |
| `mechanism-checkpoint.md` (pre-freeze) | `1b559c5c…7ea3e` (matches freeze-receipt) ✓ |
| `pre-freeze-comparison.md` (pre-freeze) | `6263e136…d8355` (matches freeze-receipt) ✓ |
| `reading-and-comparison.md` | `33786509782b8cb2719440468fd118eebcd6c079785aa1920631ae809844d1f3` |
| `adversarial-audit.md` | `1a3122a37a2ef72272b6a2f5ba83fa5ddaf33042587cde9aab197b47d0c663b3` |

I ran the author verifier `python3 -I verify.py --anchor 10665dc8…c606`. It returned `IDENTITY_VERIFIED_NOT_MATHEMATICAL_VERDICT`: 69 payloads, 11 context inputs, 35 pinned blobs and 5 retained primary files. With an all-zero anchor it returned `VERIFICATION_FAILED: external manifest anchor mismatch` (exit code 1). Per-file hashes for every input I used are listed in `input-hashes.json`.

I fetched the source myself from pinned raw GitHub URLs. All 18 preprint files match their Git blobs in the complete `sources/preprints-tree.json` (sha256 `eeecc1da…5e09b`, identical to the author's copy). My bytes for the four source sections I read in full are identical to the author's retained copies.

## 2. Target reviewed (unchanged, not weakened)

The target is a single nonempty contractible domain M⊂ℂ³ satisfying all three of the following:
- M carries a complete smooth Kähler metric with −B≤K≤−A<0 on every real 2-plane.
- M has a bounded holomorphic embedding F:M→ℂ⁵: injective, immersive, and a homeomorphism onto its image. Properness is not claimed.
- Every bounded holomorphic G:M→ℂ³ has a zero of det dG.

I judged the full conjunction. No local, compact-subset or separating-function variant was considered.

## 3. What the pinned source pays (actually read)

Source: *A negatively pinched Kähler threefold without bounded holomorphic coordinates*. I read `main.tex`, `01-introduction`, `02-reduction`, `05-logarithmic-tests` and `06-base-potential` in full, and the statements of `03-peaks` (Lemma `peaks:mean-criterion` with its proof, definition (3.x) `P_k=Σ⟨z,p⟩^k`, and Lemma `peaks:bounds` with `|P_k(z)|≤C|z|^k` on all of ℂ²).

- Theorem `main:theorem`, Proposition `base:existence`, Proposition `metric:transfer` and Lemma `map:obstruction` supply the metric, contractibility and the C³ Jacobian obstruction for M_φ.
- (5.1) `U_k=F_ε(P_k)` with `F_ε(v)=log((|1−av|²+ε²)/(1+ε²))`, so U_k(0)=0.
- Lemma `base:convergence` (local C^∞ convergence, valid for every finite L) and Lemma `base:minorant` (any L>5logQ/d₃) apply. Lemma `base:chart-estimates` holds "for every fixed finite L", and the proof of `base:existence` fixes L before λ. An **integer** L is therefore a legitimate source choice, and the author's use of it does not change the scope.
- The source records only the base coordinates z₁,z₂ as nonconstant bounded functions (§1, end of §2). It nowhere states that bounded functions separate points, that bounded functions immerse M, or that M embeds into some ℂ^N. Companion paper (introduction read in full): its H^∞-Liouville example is a different one-sided construction and contains no embedding statement. Lean doc 359 and `PinchedKahler.lean` (declaration list read) formalize only `NoBoundedCoordinates`/`MainTheorem`. **Not subsumed by the source family.**

## 4. Decomposition of the added operation

Write v_j=(1−aP_j, ε)∈ℂ². By the source's own definition, U_j = log(‖v_j‖²/‖v_j(0)‖²), with v_j(0)=(1,ε). So φ−ψ = L Σ_j log of a *normalized Hilbert norm of a holomorphic vector*.

**(a) Zero-loss scalarization.** Let e=(1,ε)/√(1+ε²) be the unit vector at v_j(0). Cauchy–Schwarz gives |⟨v_j,e⟩|²/(1+ε²) ≤ ‖v_j‖²/(1+ε²) = e^{U_j}, and ⟨v_j,e⟩/√(1+ε²) = 1−c₀P_j with c₀=a/(1+ε²). The author's "optimal coefficient" is therefore the projection onto the normalized value at the origin. The zero per-factor loss follows automatically from the source's normalization U_j(0)=0. This is the classical fact log‖h‖=sup_{|e|=1}log|⟨h,e⟩|. I confirmed the exact coefficient identity (3.2) by exact rational arithmetic in `coefficient_check.py`: 144/144 cases hold, and a shifted-c₀ control rejects 144/144.

**(b) ℓ² perturbation.** The cost of tilting e is quadratic, so square-summable tilts give a finite product of losses. This is the standard convergence criterion for products of near-unit factors (the von Neumann infinite-tensor-product or Blaschke-type condition). Normal convergence and the zeros-only-from-factors property use |P_j|≤C r^{Q^j} from `peaks:bounds`, which the source already uses in `base:convergence`.

**(c) Three generators without common zero.** DLS Lemma 2.5 (`alg-geom/9212001v3`, statement and full proof read, extracted lines 531–565) produces n+r sections. Here n=2 and r=1, giving 3. The method picks one point in each component of each rank-defect locus and requires the next section to avoid it, with Cartan B supplying prescribed values. The same dimension count works in any space of functions where avoiding countably many points is generic, by Baire's theorem. The author's version (algebraic dependence of three polynomials in two variables plus Baire on a parameter polydisc) is a variant of this count, and the author credits it explicitly. DLS asserts no weighted sup control, so it does not give (a)/(b). It does pay for "three".

**(d) Fibre embedding (z, w f₁, w f₂, w f₃).** On a Hartogs domain {e^φ|w|²<1}, a function w·g is bounded exactly when |g|²≲e^φ. This is the first-degree Hartogs coefficient criterion |g_j|≤e^{ju} used in Jarnicki–Pflug 2022, Example 2.1 and Theorem 2.2 / Corollary 2.4, which I read in the retained publisher HTML. Injectivity, immersion and the local inverse by division then take a few lines. Classical.

So the only non-credited step is applying (a) and (b) to this weight to get a basepoint-free family, then taking L-th powers. It is about one page and needs no estimate beyond what the source has already stated.

## 5. Is anything unpaid? Strongest case for SUBSTANTIAL, and why it fails

- *General machinery does not give it directly.* I checked this myself. Hörmander L² with weight e^{−(LΣU+sψ)}, followed by a sub-mean-value bound on hyperbolic balls (bounded oscillation follows from `base:chart-estimates`), gives |g|²≲e^{LΣU}(1−|z|)^{−(s+3)}. Boundedness on M needs |g|²≲e^{LΣU}(1−|z|)^{−1}, so this route loses polynomial boundary factors. Forstnerič's Theorem 2.1 and Proposition 2.2 (exhaustion, compact-open approximation, growth on shells) and his Theorem 4.1 (bounded embeddings of smoothly bounded strongly pseudoconvex domains) do not apply either. M is not of that type: it must be unbounded, otherwise the identity would contradict `map:obstruction`. This is why the step is *needed*. It does not make the step *non-routine*: the weight is an explicit sum of normalized log-norms, and (a) is the canonical way to scalarize such a sum.
- *The qualitative contrast.* The result separates "bounded embedding into ℂ⁵" from "no bounded coordinates into ℂ³" on the same pinched M. That contrast is new to this project and mildly informative: the source's counterexample does not refute the weaker "bounded complex submanifold of some ℂ^N" question, consistent with Yau's Problem 38 as recalled by Wu–Yau (JAMS 2020, p. 103). But a contribution needs a mechanism, and the campaign rules exclude headline-only novelty. The author's own pre-freeze note already lists this risk.
- *Dimension 5* equals 2 base coordinates plus 3 generators. It is not tied to an Eliashberg–Gromov/Schürmann optimality argument (Forstnerič's Theorem 2.4 gives proper unbounded ℂ^{⌊3n/2⌋+1}=ℂ⁵ embeddings for n=3, which is a coincidence of numbers only). No ℂ⁴ statement is made.

Conclusion: **TECHNICAL**. It is a correct-looking (not reviewed here) routine consequence of the source's explicit regularized-log structure plus classical scalarization, generic generation and Hartogs-coefficient embedding.

## 6. Eligibility

- **History.** I searched `frontier/iterations` (887 files), `frontier/reviews`, `findings`, `scouts`, `experiments` and the campaign markdown outside copied inputs. Terms: family/359, pinched, Hartogs, bounded holomorphic, holomorphic coordinates, Carathéodory metric, Kähler, Wu–Yau, uniformization. The only W5-related hits are the W5 packet itself, `w5-parent/initial-inspection.json`, `w5-proof-r1` (a concurrent proof gate I did not read for verdict), and ledger line 905. Structural r27 shows only a reservation ("families278/359 reserved elsewhere"). Kähler hits in I98, I102, I136 and I142 concern relative K3/Oka, MMP and packing, which are different operations. I30's Wu–Yau context is about Einstein-metric stability. **No earlier developed target.** Source screening alone is not treated as exclusion.
- **Chronology.** Feasibility reasoning was done before the freeze, and the author says so (`mechanism-checkpoint.md`, `pre-freeze-comparison.md`, bound by hash in `freeze-receipt.json`). This is honest. The freeze is not a blind pre-registration, but it is not retroactive weakening either. No eligibility defect.
- The scope was not weakened, and no prior frozen target was relabeled.

## 7. Recommendation to parent

Record W5 as technical support. Do not nominate it for a count and do not start formal or manuscript work on this verdict. Any new review round should receive this report and the author's packet unchanged.
