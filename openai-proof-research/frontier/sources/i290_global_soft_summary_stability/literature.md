# I290 literature and source contracts

2026-10-13. All OpenAI results and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. This is a scoped operation-level comparison, not an upstream truth audit or a universal literature search. Exact semantic passage hashes, complete input hashes and retrieval bindings are in `../../experiments/i290_global_soft_summary_stability/input-authentication.json`. External whole papers and entire verbatim sections are not retained here.

## Pinned family119 sources

The [main sharp soft-channel theorem](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/main.tex), label `main:soft`, already gives the arbitrary-binary-kernel contraction. Label `upgrade:production` gives the two-profile production envelope. The new proofs retain strictness in these actual operations; they do not reclassify sharp soft contraction as missing.

| File | Actual needed contracts | Semantic read extent | SHA-256 |
|---|---|---|---|
| [main.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/main.tex) | main:soft; main:energy-split; main:hybrid-profile; upgrade:production | splitlines 1–334 | `ad04285e5eaa23a9b7a897f4501176e13f139bb04811c91576d5cc717cb5f8ca` |
| [scalar.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/sections/scalar.tex) | scalar:profile-convexity; scalar:entropy-bounds | splitlines 1–219 | `03b64ba1af8ce45b6d4670c0cf919abc119838e9624e06c5c0e2c720032007cb` |
| [canonical.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/sections/canonical.tex) | canonical:priced; canonical:coverage; canonical:reflected; canonical:onecorner | splitlines 1–310 | `fc449aa1321ed2fd73b4791311a6f61f4de16a99609021e3a94ebcbb381a0ed7` |
| [capacity.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/sections/capacity.tex) | capacity:onebit; capacity:refined | splitlines 1–116 | `f0a33b2ce10a3055f8333bf817e779417be9819b3acf519008bc26ce07c9f53c` |
| [reserve.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/sections/reserve.tex) | reserve:pooling; reserve:payment; reserve:capacity; reserve:corner-margin; reserve:joining | splitlines 1–291 | `2b4c8b10712f4c15a4e3787c9e0f9687d6020110987f50b1612a3139f221171c` |
| [thinning.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/sections/thinning.tex) | thinning:derivative-loss; thinning:window-bound; thinning:payment; thinning:high-value | splitlines 1–165, 355–493 | `c52291a2068e607bf09e56761a6e8c0c6ef75b24c3d33385f45899f7a4b96cc8` |
| [upgrade.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/sections/upgrade.tex) | wall:monotonicity; upgrade:original-child-pooling; upgrade:joining | splitlines 1–284 | `2c0d5677a9dbc7a070dea066b50ceca5e0655fa1beb9cddb0d5f312274a09947` |
| [flow.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/sections/flow.tex) | flow:sharp-trajectory and positive-time integration | splitlines 1–116 | `9065dd3bd4bf33f66547e58c0a39c5841103f48d134cbe9eea392ec5289653c1` |

The [Hellinger companion main](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hellinger-contraction-with-arbitrary-Boolean-output-bias-September-24-2026/build/main.tex) has Boolean contract `thm:main`, arbitrary output bias, and a square-root profile. Read main lines 1–195; SHA-256 `b286e05e0e9321c4a0cb925734a078b127e9d8694e8fccc5d4f6a484bfb0347b`. Its included proof files are not imported. It is not a supplied soft exact-information stability theorem.

The capacity snapshot is one limited pinned file; the main excerpt is only the soft theorem contract. Neither is an external whole paper.

## Current exact primary comparisons

| Primary source and current version | Needed statements/proof interface | Current mathematical-text SHA-256 |
|---|---|---|
| [Ky–Tran stability](https://arxiv.org/html/2609.31797v1) | Theorem 1.1; equations (2.2)–(2.3); Lemma 3.3; Lemma 5.1 and Propositions 5.2/5.4. The main theorem and endpoint budgets are Boolean. | `3b55b85df872452ea83e128a4124355b8d5d87eb928b27cb3302f3aee0393947` |
| [Ky–Tran companion](https://arxiv.org/html/2609.24184v1) | Theorem 7.1 and Lemma 7.3 have bounded/real-field scope; Lemma 4.4 is an edge inequality. Theorem 4.5 integrates its clock from the Boolean zero-entropy endpoint. | `89c122e5fbdf3629b5ba5c9797547c31c6d68191dcc4051531306bf8bd4d5eae` |
| [Chen et al.](https://arxiv.org/html/2609.24931v2) | Lemmas 8.1 and 9.2, unrestricted induction and the semigroup deduction: arbitrary channels are included; the needed global deficit-to-coordinate estimate is not supplied by those operations. | `522261bc5200556213b25697977f4cbea264eb4efbdcb8a5e53db206b1a0d276` |
| [Yu](https://arxiv.org/html/2410.10147v5) | Theorems 4.1, 4.2 and 4.5, local reduction and Lemma 4.4: balanced Boolean local optimality. No soft global entrance follows from these statements. | `d37c56f7300399fe9cc9db55e7249356d3ab9a846db3f6819a874c5f71120fbf` |

Fresh version pages still list stability v1 (25 September 2026), companion v1 (21 September 2026), Chen v2 (24 September 2026), and Yu v5 (7 April 2026). The URLs are their exact arXiv identifiers, not search-result links. Their short version-page records and full retrieved byte hashes are bound in the authentication JSON.

Ky, companion and Yu HTML bytes match I131. Chen raw HTML differs; re-extracting the current response using I131’s deterministic extractor gives exactly the same mathematical text. This is not a certificate, TeX or formalization identity claim. No external computer certificates were executed.

## Additional primary proof inputs and the user’s LSI lead

[Mossel–O’Donnell–Oleszkiewicz, published Annals source](https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n1-p05-p.pdf), Theorem 3.18 under Hypothesis 4, Propositions 3.11–3.12 and the complete matching-moments replacement proof: bits and Gaussians have matching first three moments, and fourth-moment hypercontractivity bounds the fixed-degree replacement error. Theorems 3.19–3.20 clarify clipping and smoothing. This is classical transport machinery; I290 reproduces its needed calculation and pays the entropy/mean/noise transport. PDF SHA-256 `9921329b11b0343888adf35ad7a0257655340f27cc6f14775def083639cc2f2c`; `pdftotext -layout` output SHA-256 `a8722551e526bfb1abe03aada353edcf5aa278b05d28fe7ad494626d875e4d95`. Read ranges are bound individually. The full paper/extraction is not saved.

[Eldan–Lehec–Shenfeld actual v2](https://arxiv.org/pdf/1903.04522v2): Corollary 2 has a second-moment matrix hypothesis; Theorem 3 distinguishes small covariance eigenvalues; Theorems 6/8 have different mixture/decomposition conclusions. Theorem 1 and the scaling/Cramér–Rao proof were read. A pooled posterior covariance bound does not furnish the separate posterior hypotheses or the reserve GP290. PDF SHA-256 `62bce8b52e7b0cdbddbf3ba45621a6169b0b0d7bbd1e668b8fbf66d32b1a9cca`; extracted text SHA-256 `1e785ee99b6f7e5c94f7a86f072502c8937b732578d3ef17e5adfa86c0201ea2`.

[Fathi–Indrei–Ledoux author-hosted primary manuscript](https://www.normalesup.org/~mfathi/docs/LSI14.pdf): Theorem 1 and Corollary 2 require a posterior Poincaré inequality; the complete OU proof uses that condition on the evolved log-density gradient. Theorem 5 has a different transportation conclusion. Upper density bounds and the complementary-mixture identity are not substituted for its hypotheses. PDF SHA-256 `8a08007e16e42421ab3a2914b0e55387cfada6cf89b9885e19e5e2e3df7b4278`; extracted text SHA-256 `527ddf134fd5d017efb9a7c3a1d03abe6aca556d014fc11a04b04b2e97fbdc29`.

The new complementary-density identity is derived directly in analysis §5. A positive standard LSI gap alone leaves the required nonlinear reserve F(I)−2I unpaid. GP290 states the precise stronger production inequality; G290 states its sufficient finite-noise alternative. Neither is established by the inspected primary inputs. No universal Gaussian equality/stability theorem is assumed.

## Contribution boundary

I290 adds marked joining equality/compact-law rigidity, global stability throughout every fixed positive singleton sector, diffuse-only failure reduction after compression, and a proved transfer from diffuse soft cube fields to Gaussian fields. Its dependencies are explicitly inherited or classical. S128, G290 and GP290 remain unresolved. This is a new-to-this-round deduction claim, not a worldwide novelty or acceptance claim.
