# Independent Bergman-conjecture review

Reviewer: matrix_extension. Date: 2026-10-26. Author: polynomial lane. This is an independent mathematical/source/prior-art review, not an audit of a completed Lean certificate.

**Verdict: mathematical proof PASS; exact-source scope PASS; provisional novelty gate favorable under the documented-prior/no-known-resolution standard. Proceed to a full source certificate. No formal-completeness or discovery-count approval is supplied by this report.**

## Reviewed target and source

MathDB 368572, UUID `8e6959b8-e99a-4f2e-b5fa-88c0963e0a87`, has no posted solution in the retrieved live snapshot. The target is Edholm–Mathew, *Arithmetic properties and zeros of the Bergman kernel on a class of quotient domains*, Conjecture 4.20. I read the actual latest arXiv v3 and the actual full published article, Math. Z. 313 (2026), article 43, published June 6, DOI [10.1007/s00209-026-04059-8](https://link.springer.com/article/10.1007/s00209-026-04059-8). The latter PDF is SHA256 `4b31a9ab6b01523058f9c336bdf3f93743589a1ae8e41b4d06197fefe34de71e`; its page 25 was also visually inspected. The arXiv history lists v3 as latest. All retrieved sources and provenance are inventoried in `provenance.json`.

The full target is nonvanishing of the specified polynomial on the unit circle for every pair of coprime positive integers m>n, with the resulting allocation of m−n roots inside the punctured unit disc, counted with multiplicity. This is one result. The known differences 1,2,3,4,6, numerical examples, root-allocation corollary and kernel interpretation are not additional discoveries. The latest primary retains the conjecture and expressly describes the difference-5 case as open; it mentions related work in preparation. That unlocated manuscript remains a disclosure limit below.

The literal source polynomial is recoverable from Proposition 1.10, equation (1.11), using the triangular coefficients D_m of (1+X+⋯+X^(m−1))². For 0≤r,q≤2m−2, retain the terms satisfying q−nr≡n−1 modulo m and use the exponent

    β=(q−nr−m−n+1+2mn)/m

in P(s,t)=Σ D_m(r)D_m(q)s^r t^β. The source defines Q(z)=z^(1−2n)P(z,z). I checked this against the source's separate five-piece ceiling formulas (3.21), including their exponent shifts. The candidate is not a different numerator normalization. The relevant source result is labelled **Proposition** 1.10 in the published article. A nearby published proof has an index typo in a repeated formula; the candidate uses the correct proposition formula and does not derive its result from that typo.

The reviewed proof is preserved as `BERGMAN-PROOF-CANDIDATE.reviewed.md`; its exact hash is bound in `provenance.json`. This report covers its full algebraic argument, including the subsequently appended direct combinatorial proof.

## Independent algebra and strictness check

Put k=m−n and S(w)=Σ_(p=0)^(m−1)w^p. For primitive mth root ω and unit a,b, set s=ab^n,t=b^m. The root filter gives

    b^(m+n−1−2mn)P(s,t)
      = (1/m)Σ_j ω^((1−n)j)S(aω^(−nj))²S(bω^j)².

This selects precisely q−nr+1−n≡0. On the unit circle S(u)²=u^(m−1)|S(u)|². The remaining phase is ω^((1−n)jm)=1, so the normalization is exactly

    P(s,t)/(s^(m−1)t^n)
      = (1/m)Σ_j |S(aω^(−nj))|² |S(bω^j)|².

For any unit z, choose b^m=z and a=zb^(−n). The left side is z^(−k)Q(z), with no missing scalar or extra monomial.

Strict positivity is valid at every unit z. If z≠1, every second factor is nonzero by (1−u)S(u)=1−u^m. If a^m≠1, all first factors are nonzero as well; if a^m=1, coprimality makes some aω^(−nj)=1 and S(1)=m≠0. At z=1, choose j with bω^j=1; then the first argument is also ab^n=1. Thus a positive term exists even at all exceptional resonances. Rational geometric-quotient formulas must be interpreted through the finite polynomial S at these points; no division-by-zero extension is assumed.

The finite alternative is equally valid. Define e_r(p)=p−floor((np+r)/m) and A_r(z)=Σ_p z^e_r(p), with p,r in 0,…,m−1. The inequalities 0≤e_r(p)≤k hold throughout, so

    Q(z)=Σ_(r,p,p') z^(k+e_r(p)−e_r(p'))

is an ordinary polynomial identity. On |z|=1 this is

    z^(−k)Q(z)=Σ_r |A_r(z)|².

I independently checked a direct source-to-SOS bijection, without assuming Parseval or importing the author's polynomial code. Expand both D_m factors as ordered geometric-index pairs. Complement each second index by m−1. The source congruence then becomes equality of residues q−np≡q'−np' modulo m. For residue r, the unique q in 0,…,m−1 is np+r−m floor((np+r)/m). Substitution into the literal source exponent gives exactly k+e_r(p)−e_r(p'). This proves the identity for arbitrary m,n; the complement operation is invertible and preserves all term multiplicities.

Coprimality supplies a unique p* in 1,…,m−1 with np*≡m−1 modulo m. Write np*=mq*+m−1. Only this summand changes between A_0 and A_1, giving

    A_1(z)−A_0(z)=z^(p*−q*−1)(1−z).

The exponent is nonnegative. Hence for nonzero z≠1 the two polynomials cannot vanish simultaneously, while A_0(1)=m. This establishes the required strictness independently of the root-filter argument.

The same finite polynomial has degree exactly 2k and nonzero constant coefficient: A_0 has both exponent 0 (at p=0) and exponent k (at p=m−1), so the two extreme terms of Q have positive coefficients. Swapping p and p' proves reciprocity. The usual reciprocal-root pairing, with multiplicities and no zero root, therefore gives exactly k roots in the punctured unit disc after unit-circle nonvanishing. A formal claim of this root count must include the corresponding polynomial and multiplicity bridge, rather than merely supply the positivity lemma.

`check_bijection.py` is my independent exact-integer corroboration. All 71 coprime pairs with 2≤m≤15 passed the full four-index source expansion, complement-pair exponent, grouped SOS, A_1−A_0, extreme-coefficient and reciprocity checks. Result SHA256: `57d42249d7b21bd892713a87c6532c1c868b7c9c02bd631774200c95106f360a`. This finite computation is not the proof of the universal claim; the algebra above is.

## Nearest prior work and the novelty boundary

**Almughrabi 2023 already contains the weighted root-of-unity numerator identity.** I read arXiv 2303.14268v1 and then the full actual published body of *Bergman Kernels of Two Dimensional Monomial Polyhedra*, Complex Anal. Oper. Theory 17 (2023), 103, DOI [10.1007/s11785-023-01401-4](https://link.springer.com/article/10.1007/s11785-023-01401-4). Normal access returned all four sections with an institutional-access banner; no access bypass was used. Published HTML SHA256 is `b55d3ed9fa901a876ff4540a703d6929dd89ed7fdea9bbba085342653b5f3b29`. Equation (24) explicitly gives the same weighted root sum h(A,B), up to reversing the root index. The following equations derive its covariance and extract coefficients. Proposition 2 supplies the older kernel numerator formula. There is no claimed unit-circle positivity or full root allocation in the body I read. A later request for its PDF returned a challenge, but the full published HTML, including equation (24), was available and read. The old identity deserves prominent explicit credit; it cannot be presented as newly discovered.

I also read the full author manuscript of Chakrabarti–Konkel–Mainkar–Miller, *Bergman kernels of elementary Reinhardt domains*, Pacific J. Math. 306 (2020), 67–93. Its relevant statements calculate rational kernels; I found no full same-polynomial unit-circle nonvanishing theorem.

As an additional independent nearest-prior screen, I read the full arXiv HTML and public NSF author PDF of Chakrabarti–Cinzori–Gaidhane–Gregory–Wright, *Bergman kernels of Monomial Polyhedra*, arXiv 2308.05834v1; journal reference J. Math. Anal. Appl. 531 (2024), 127723, DOI 10.1016/j.jmaa.2023.127723. The main theorem and §4.7 establish a canonical rational representation with no common polynomial factor between numerator and denominator. The proof uses boundary-diagonal blowup to rule out such factors. This is not pointwise nonvanishing of the numerator on a unit torus, and does not give the conjectured conclusion. Its §5.2 recovers Almughrabi's formula. The NSF PDF is SHA256 `79cc323e404e20bc597d5c42f7fb12c4f8f8d9d858eff6c8584aeb902f213f7f`; it is an author manuscript, not asserted byte-identical to the final journal article.

Targeted searches of the exact conjecture, source title/arXiv ID, author names, unit-circle nonvanishing, quotient-domain polynomial zeros and sum-of-squares routes found no independently published full resolution. The latest target publication itself still calls the result conjectural. The source-mentioned follow-up in preparation was not located or read; this report does not establish priority relative to unpublished work, or exhaustive absence of every possible earlier implication. No authors were contacted and no external posting was made.

The proposed new conclusion is the full resolution of the explicitly open all-coprime-pairs conjecture, through strict positivity of the normalized diagonal numerator. Classical finite Fourier orthogonality, geometric sums, reciprocal-root pairing and Almughrabi's identity receive no new-discovery credit. That the route is elementary does not make it an already published resolution. Conversely, discovery of an older theorem explicitly giving this full strict positivity or root allocation would exclude the candidate. On the actually read sources, no such theorem was found.

## Formalization acceptance conditions

The mathematical and bounded literature screen support continuing. A final Lean review must independently compile frozen modules, inventory every local declaration and standard axioms, and check that the unconditional endpoint quantifies over all coprime positive m>n and the literal source Q. No supplied SOS, coefficient-identity, exponent-bound, nonzero-constant or reciprocity hypothesis may replace their proof. If root allocation is claimed as formally certified, multiplicities and the punctured-disc count must also be proved. There is presently no Lean PASS claim in this report.

Signed: matrix_extension, independent review, 2026-10-26.

## Frozen source-nonvanishing formal review, 2026-10-26

**PASS for the complete source nonvanishing endpoint.** I independently read all seven frozen modules, copied their exact bytes into this owned lane, and compiled them afresh in an isolated directory with pinned Lean 4.34.1, warnings as errors, and the assigned pinned dependency build. Every one of the 47 local declarations was inventoried and its axioms printed. Only `propext`, `Classical.choice`, and `Quot.sound` occur; no proof holes, custom axioms, unsafe declarations or native decision procedure occur. The isolated receipt is `build/fresh-audit-_etvtgyh/receipt.json`, SHA256 `d1e7aac31e5db7e1b121aa5dc8618fd76457a3aba1ad870482df8abab1da8a8e`.

Frozen modules and SHA256 bindings:

| Module | Declarations | SHA256 |
|---|---:|---|
| BergmanConvolution | 7 | `6935d787b9b9454951fc7f3036fa29b6d2d86364ea9245dbbfca79b7c5392e13` |
| BergmanSource | 13 | `405de30d9a22a89f848fc3070c7658881fb4295209d07f5c6e763df5b80b4a73` |
| BergmanFloor | 9 | `aba14a986126e82cc8ef8929bff721d351f792cc07258986a3374d1d7a4212a8` |
| BergmanResidues | 7 | `6a2d1a13b3cd2eb1e0e4eff4b5ffcf4e70ff8500e5a7184b11343d05720d6708` |
| BergmanGram | 2 | `7131c8f8a73bc04e6a2b8f4e6e92a7b2496c1d08381754ddddfa3252202c39b6` |
| BergmanWeight | 5 | `a4d16f8b5ed04dc95604f229f0ee5042d7e79b47880193744ac07c51537b0a69` |
| BergmanSOS | 4 | `ac59aaaeec4be6f8c59e2933d8d49f87f6c88eef99af3fbf0623290e8b82bc23` |

`BergmanSource.sourceP` is the literal two-dimensional finite source numerator, with its signed triangular index, zero extension, and stated support box. The row reindexing proves existence, uniqueness, divisibility and support for each nonzero term. `sourceQ_eq_compressedQ` proves the diagonal exponent normalization for every nonzero input, without a coefficient or SOS premise. The convolution module counts all ordered pairs, including repeated indices and zero coefficients. The floor module proves uniqueness/existence of the carry index and the full A_1−A_0 identity; it does not assume nonvanishing. The residue and Gram modules group exactly the four finite indices. The weight module proves the reflected congruence and the **integer** exponent identity before converting negative powers to conjugates on the unit circle. Thus no natural-subtraction truncation changes the source exponent. The final `sourceQ_sos` and `source_conjecture_368572` require only 0<n<m, coprimality where needed, and norm z=1. This is the full nonvanishing statement, not a sufficient lemma under supplied source identities.

Root allocation is not yet part of these seven modules. `sourceQ` is a Laurent-normalized function definition; its unit-circle nonvanishing is correctly certified. A claim that the actual ordinary polynomial has exactly m−n punctured-disc roots with multiplicities still needs the separate ordinary-polynomial evaluation, degree, constant coefficient and reciprocity bridge. I am authoring a generic reciprocal-root allocation lemma at the parent's request, so that new helper will require another reviewer rather than my own independent authorship assessment. My independent review of the seven modules above remains separate from that helper.

## Draft manuscript review and authored helper status

I independently read the entire polynomial-lane draft `third-discovery/main.tex`, SHA256 `6b74a352750e08732afc4bc20eaed07b4d5e1d53fd74029296139cac3d843410`. **PASS for mathematical, source and claim scope at these bytes.** Its source coefficient formula, divisibility and support bounds, integer exponent, finite bijection, strictness, phase normalization and reciprocal multiplicity argument all check. The kernel consequence also checks: the stated Z,W realize the products s=t=z, both lie in the domain because 0<|z|<1 and m/n>1, and t^n−s^m=z^n(1−z^(m−n)) is nonzero. The prior Almughrabi identity is explicitly credited. The unpublished follow-up limit is disclosed. The current seven-module/47-declaration scope accurately distinguishes the certified nonvanishing endpoint from the additional polynomial-degree and multiplicity modules then being developed. That coverage paragraph and final manifest must be rebound if integration changes the formal scope or text. I did not author this manuscript or its reviewed seven modules. PDF layout was not reviewed here.

Separately, at the parent's request I authored `root-allocation/BergmanRootAllocation.lean`, SHA256 `bece6ca9ff8c7f0a3b4c99ea6af6c85bbfbecc0bc02ccfc98dd1f7caf2ce3c49`. It imports only Mathlib. Its theorem `BergmanRootAllocation.reciprocal_root_allocation` proves, for p:ℂ[X], degree 2k, p.reverse=p, nonzero constant coefficient and no unit-circle roots, that the multiset of roots filtered by z≠0 and norm z<1 has cardinality k. Exact reciprocal root **multiset** equality is proved through factorization and reverse-linear factors; no simplicity or distinct-root hypothesis is used. All five local declarations passed a fresh isolated pinned warnings-as-errors/axiom audit, receipt `build/fresh-audit-lf6gyjtm/receipt.json`, SHA256 `ade5175976cfc3fbe374cc3c2feb4e83664d8b81845766b7f4f1fcae06f9e050`, with only the standard three axioms. This is an author compilation report, **not an independent review** of that helper. The parent will review it and the source ordinary-polynomial bridge separately.

## Final ordinary-polynomial and complete-source review

**PASS for the full source scope, including the ordinary polynomial and multiplicity count.** This supersedes the earlier pending polynomial/count coverage qualification. I independently read the parent's frozen `BergmanPolynomial.lean` (23 declarations), SHA256 `e76ad1bcebd8b7c0a4c2a3773849cb22b6254dfcc83eae7d4dbd446e08d71bba`, and `BergmanConclusion.lean` (3 declarations), SHA256 `ea781465a95c7a0c6809b8bf44981af13ed5bd37cc9bb15081fc367f2a28f02a`. I did not author either module.

For each selected pair of triangular indices, divisibility is proved before integer division is converted to an exponent. `exponent_mul` gives the exact numerator identity, and `exponent_bounds` proves 0≤E≤2(m−n) for every selected index in the source support. Thus conversion with `Int.toNat` cannot truncate a negative selected exponent. The polynomial is first defined over ℕ, so its positive extreme coefficients cannot cancel. The explicit constant term uses r=0,q=n−1, with exponent zero and two positive triangular coefficients. The explicit top term uses r=2m−2,q=2m−n−1, with exponent 2(m−n); both indices satisfy the source support bounds. The complex coefficient map is injective on ℕ. These prove exact degree and nonzero constant coefficient for every 0<n<m, without a coprimality assumption for those algebraic facts.

The complementary index map sends (r,q) to (2m−2−r,2m−2−q). It preserves the selected congruence and both triangular coefficients, and sends the exact integer exponent to 2(m−n)−E. The proof checks exponent bounds before applying polynomial reflection, and reindexes the entire finite sum. Consequently it proves the actual `polynomialQ.reverse = polynomialQ`, rather than assuming reciprocal roots or a boundary-only symmetry.

`polynomialQ_eval_source` identifies this ordinary polynomial with the literal normalized source expression at every nonzero complex argument. Its value at zero is supplied by the correct ordinary-polynomial extension, not the zero value that a totalized negative power might give to a Laurent expression. Agreement away from zero identifies exactly the source's polynomial Q; the root count uses `polynomialQ`, never a Laurent-function surrogate. The final `source_full_conjecture_368572` has only 0<n<m and coprimality as hypotheses and joins unit-circle nonvanishing with

    ((polynomialQ m n).roots.filter (fun z => z ≠ 0 ∧ ‖z‖ < 1)).card = m−n.

The use of the root multiset retains all algebraic multiplicities. There is no distinct-root or simplicity condition and no source-identity, degree, reciprocity, SOS or root-count hypothesis left to supply.

I freshly copied and replayed all ten frozen modules together, including the authored generic helper, in `build/fresh-audit-gtdu38ag/`. All **78** declarations passed warnings-as-errors compilation and complete type/axiom inventory; only `propext`, `Classical.choice`, and `Quot.sound` occur. This combined replay is independent execution for the whole packet; mathematical authorship independence applies to the 73 declarations outside my five-declaration helper. The parent separately read and replayed that helper and is responsible for its independent review. The receipt and exact module hashes are preserved in `build/fresh-audit-gtdu38ag/receipt.json`, SHA256 `a1e2ed83b7215be10799111664163700dac478f83ebad3250c681a262d640255`. All ten files were byte-compared against the final candidate formal directory and match.

I also reviewed the exact final integrated manuscript `candidates/bergman-unit-circle/main.tex`, SHA256 `f9aa7304be02763a951f9c7d66b946b054c8725735b04ea18cec5cf4f7cc50fb`. **Final manuscript scope/math/source verdict: PASS.** Its mathematical text matches the independently reviewed draft; the replaced formal-scope paragraph correctly reports ten modules, 78 declarations, the ordinary-polynomial bridge, exact multiplicity count, compiler pins, and the restriction of the formally certified SOS to unit inputs. The general Laurent identity and complex-analytic consequence are proved in prose and are honestly distinguished from the certificate's polynomial/finite-algebra coverage. No PDF-layout verdict is supplied here. The prior-art recommendation remains favorable under the bounded standard and the disclosed unlocated in-preparation work; this is one source-conjecture outcome.

Signed: matrix_extension, independent review of the source, manuscript and nine externally authored modules; author compilation status only for BergmanRootAllocation. Date: 2026-10-26.

Final layout-only binding: the final TeX SHA256 is `74fdb087ec5dc1dd33049f647481d50923d85f6d064fcbd5ecc5d9bf2428e48c`. I verified that changing only `top=.8in,bottom=.8in` back to `.9in` reproduces the reviewed `f9aa7304…` hash exactly. All mathematical text and formal-scope statements are unchanged, so the final manuscript PASS applies to these bytes. Parent handles PDF layout QA.
