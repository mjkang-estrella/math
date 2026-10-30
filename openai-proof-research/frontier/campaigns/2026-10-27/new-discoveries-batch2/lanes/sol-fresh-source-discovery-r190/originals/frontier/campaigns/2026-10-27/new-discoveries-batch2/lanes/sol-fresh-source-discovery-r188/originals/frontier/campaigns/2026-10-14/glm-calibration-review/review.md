# Independent GLM calibration review

2026-10-14. **Verdict: finite-algebra core reproduced; two checker repairs required.** The calibration supports using GLM for bounded implementation and exact-checking work **with independent mathematical and code review**. It does not validate GLM as the sole verifier, establish general model reliability, or add a new finding. R019 is an old accepted result and remains so; the defects below are in this calibration checker, not in R019's proof.

## Scope and reproduction

Read project AGENTS.md; the R019 entry and relevant scope notes in TWENTY-FINDINGS.md; the full R019 finding/proof; the actual I287 analytic source, including its separate optional scalar-polynomial scope; the I291 review and its reading/source records; and all of GLM's report, checker and result tables. Retrieved the pinned direct-Crouzeix primary TeX at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and read lines 37–76, including `thm:main` and the explicit base-first convention. Upstream truth is stipulated; the elementary R019 norm certificate itself needs no upstream inequality.

A byte-identical copy of the original checker was executed with `/tmp/sympy-venv/bin/python` (SymPy 1.14.0), with this review directory as its working directory. This preserves the original files, since the script writes `results.json` in its current directory. Exit code: **0**. The original result and rerun have identical statuses and details for all baseline checks and all mutation checks, ignoring only timings and generation metadata. All original GLM input hashes remain unchanged.

- Baseline: 21 reported PASS, zero exceptions.
- N12 mutant: 13 FAIL / 8 PASS; declared expected fail/pass subsets satisfied.
- N56 mutant: 13 FAIL / 8 PASS; declared subsets satisfied.
- Each polynomial mutant: 8 FAIL / 13 PASS; declared subsets satisfied.
- No mutation failed through an exception; all observed failures are ordinary failed comparisons.

See `validation.json`, `rerun.stdout.txt`, copied `subject-check.py`, and rerun `results.json`. Hashes bind this review to those exact bytes.

## Defect 1: the tensor negative control is not the advertised tensor product

In original `check.py`, lines 238–254, `build_PN_fiberfirst` uses indices `2*j+i` and `2*jp+ip`. A genuine fiber-first `C²⊗C⁶` assembly must use **`6*j+i` and `6*jp+ip`**. The implemented indexing collides and leaves the last four rows/columns unused. Therefore the reported `Tensor_convention` PASS checks a malformed matrix, not the advertised `Σ C_k⊗N^k`.

Independent exact checks in `audit.py` establish:

1. The **base-first** builder equals `Σ kronecker_product(N^k,C_k)` exactly. The principal R019 evaluation is correct.
2. The malformed negative-control matrix differs from the true fiber-first matrix in 20 entries.
3. For the true flip permutation `J_(6j+i,2i+j)=1`, the correct fiber-first matrix F satisfies `F=J P[N] J*` and `F(Jx)=2(Jy)`.
4. F does fail the attainment equation if one incorrectly retains the unpermuted base-first coordinate vectors; thus a properly implemented convention negative control is available.

Both tensor orders describe the same operator after consistent basis permutation. The defect does not invalidate the baseline norm, spectrum, grading or attained vector calculations, which use the correctly checked base-first builder. It does invalidate the calibration report's claimed coverage of that particular negative control.

**Repair required:** use stride six or a genuine Kronecker assembly in the negative control, and test both the flip identity with permuted vectors and the intended mismatch with unpermuted vectors. Correct its description from an intrinsically “wrong convention” to inconsistent coordinate interpretation.

## Defect 2: rank computations under mutations silently reuse baseline N

Original lines 284–296 define `words_upto(L)` using `build_N()` internally, with no matrix argument, and cache only by L. `cert_Cyclic_rank(N,Cks)` then calls this helper at lines 626 and 649. Thus the cyclic-word ranks and algebra-span dimensions are always those of baseline N, even when the certificate receives a mutated N.

The later vector-identity checks do use the actual argument, so the aggregate `Cyclic_rank` certificate can still fail under an N mutation. This does not repair the rank-component coverage: a zero-matrix input still reports cyclic ranks `1,2,3,5,6,6` and `dim6=36`, whereas its actual cyclic dimension and unital algebra dimension are both one. The aggregate certificate rejects zero only because its separate vector identities fail.

Consequently the report's sentence that cyclic rank remains six under the four mutants is **not established by the reported rank calculation**. It may be mathematically true for those mutants; no such conclusion is taken from this implementation.

**Repair required:** parameterize word generation by the actual N and N*, and either remove caching or key it by an immutable matrix identity and L. Add the zero-matrix control and a reducible nonzero control so that baseline reuse is immediately visible. Keep cyclicity and full-algebra dimension as separately reported fields.

## Baseline irreducibility is independently certified

This defect does not undermine the baseline span-36 assertion. I independently conjugated the pair `(N,N*)` by

`D=diag(1,1,1,sqrt(14),sqrt(14),sqrt(7))`.

Both `D^(−1)ND` and `D^(−1)N*D` have rational entries, retained in `targeted-results.json`. Exact rational word-space dimensions through lengths 0,...,6 are

`1, 3, 7, 15, 26, 34, 36`.

An explicitly listed 36-word basis has flattened 36×36 determinant

`2733816767052433962421431 / 576460752303423488 ≠ 0`.

Every basis element is a word in the actual transformed generators. Thus their complex algebra is all of M_6(C), and simultaneous similarity transfers that span statement back to N,N*. Any reducing projection commuting with N and N* commutes with every matrix, hence is zero or identity. This is a genuine exact finite irreducibility certificate; cyclicity of one vector alone would not suffice without the additional argument in R019.

The full word list, multiplication convention, determinant, rational generators and reproducible `audit.py` are supplied. The argument does not rely on the broken mutation cache.

## Exact arithmetic, expected values and universal claims

The finite-algebra core computes from N and the polynomial coefficients, then compares with displayed target values. Hard-coded expected values do not make such checks circular when the left sides are independently multiplied or symbolically expanded. In particular the support-pencil characteristic polynomial is reduced symbolically modulo `c²+s²−1`, rather than sampled at angles; the boundary identity is reduced modulo `zw−1`; the complete 12×12 Gram characteristic polynomial is computed directly.

The following limits matter:

- `N_structure` compares a matrix built from `N_SPEC` with that same specification. It is an input/mutation consistency check, not an independent mathematical certificate that the transcription agrees with the paper. I compared the six entries and zeros with R019/I287 directly.
- The scalar-compression PSD checks cover exactly 36 selected pairs of complex unit vectors. All principal minors are examined and radical signs use rational interval enclosures, not floating-point thresholds. They do **not** prove the universal quantifier. GLM explicitly discloses this limitation in both report and JSON; there is no false claim of a sampled universal proof.
- The universal R019 argument instead uses the one-dimensional top singular line, its flat Schmidt coefficients, the exact complementary bound 337/128, and output contraction. I checked the source reasoning and independently verified the exact Loewner inequality
  `P[N]*P[N] ≤ (337/128)I+(175/128)xx*`.
  The half-overlap arithmetic is `4/2+(337/128)/2=849/256`. This identifies why the finite ingredients support the existing analytic proof, without representing the 36 samples as its proof.
- `psd_hermitian` assumes Hermiticity but does not test it. A non-Hermitian triangular matrix with positive principal minors is accepted by this helper. **No current calibration call violates its precondition**: all calls form `alpha I−M*M`. An explicit Hermiticity guard is recommended before reuse as a general utility.
- `run_battery` converts exceptions to FAIL, and the mutation consistency logic would accept an exception on an expected-fail certificate. No such exception occurred in this run. Future checker use should distinguish an expected mathematical mismatch from an execution error.

The maximum-principle extension to the disk, convexity/support interpretation of the numerical range, and the full universal scalar-compression argument remain mathematical proof steps. GLM labels those out of its finite checker scope. Its calibration also does not check I287's separate original-resolvent boundary-field certificate or optional scalar-polynomial theorem. No coverage of those statements is added here.

## Mutation assessment

All four specified mutations genuinely alter exactly the stated entry or coefficient and are recomputed through the current builders. They are not fake failures caused solely by comparing mutation metadata. The polynomial changes preserve support, so grading correctly survives. N12 does not enter the sole length-three path `N14·N45·N56`, hence N³ and N³N*³ remain unchanged. Independently recomputing the N12 mutant confirms that the attainment equation breaks despite that survival.

GLM candidly records a wrong initial expectation for N12's effect on the attainment/outer blocks and six checker bugs corrected during development. The final expected sets are therefore corrected, retrospective dependency sets, not a pre-registered prediction test. This is acceptable evidence of iterative implementation work, but cannot be used to claim flawless prior dependency reasoning. The two remaining defects found by this review reinforce the need for independent checking of harnesses and negative controls.

## Deployment recommendation and disposition

This one trial supports a **bounded, reviewed implementation role**: translate a precise mathematical specification into exact algebra, generate candidate certificates, run reproducible checks, and expose failed dependencies. The exact primary norm/spectrum computations are useful and reproducible. Assignments should retain parent/human mathematical review plus independent code review of parameter propagation, caches, tensor strides, negative controls and quantified coverage.

Do not describe the current checker as an entirely correct 21-certificate independent reproduction until the two required repairs are made and rerun. Do not infer general GLM reliability, frontier proof ability or sole-verifier suitability from this trial. No new substantial-result credit is earned, no original GLM artifacts were edited, and no acceptance/index/commit/publication state was changed.
