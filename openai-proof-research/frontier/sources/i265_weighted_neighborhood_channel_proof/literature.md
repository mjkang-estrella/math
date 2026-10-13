# I265 primary correctness dependencies

This is a correctness-only source record for I264's weighted-neighborhood theorem. All OpenAI results at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. They were not truth-audited. I265 makes no contribution, acceptance, finding-count, or worldwide-priority assessment.

## Pinned equality contract

*Equality cases in the sharp one-dimensional matrix Lieb–Thirring inequality*, `build/sections/introduction.tex`, [exact pinned primary section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026/build/sections/introduction.tex).

All 161 lines were read, and fresh HTTPS bytes agree with the retained fully read excerpt `equality-introduction.tex`: 8,251 bytes, SHA256 `296070a983ced0094a761b41562a7eda1e24471d885b84118c3a56227b35b002`. Theorem `thm:main` specifies measurable Hermitian positive semidefinite finite-matrix W, integrable ordinary tr W^(gamma+1/2), the full negative-eigenvalue moment with multiplicities, sharp C_gamma, and the equality solitons (r+1)a² sech²(ra(x-x0)). Each nonzero scalar equality channel has exactly one negative eigenvalue -a². These supply the fixed cost C_gamma integral w^p=a^(2gamma). The quantitative-defect discussion was read but is not used as a stability premise or assessed for overlap. The remaining upstream proof was not read or audited.

## Pinned matrix companion contract

*Sharp one-dimensional Lieb–Thirring inequalities for matrix potentials*, `build/sections/introduction.tex`, [exact pinned primary section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-one-dimensional-Lieb-Thirring-inequalities-for-matrix-potentials-October-5-2026/build/sections/introduction.tex).

All 106 lines were read. Fresh HTTPS bytes match retained `matrix-introduction.tex`: 5,720 bytes, SHA256 `72dedb3dd3e00cd1e9e3db45c1bc9080f42006ff654cea6a18a98537528a8b60`. Theorem `thm:main` confirms the same measurable finite-matrix full-moment class, exponent interval, sharp constant and ordinary trace. No noncommuting-potential or rank restriction is added upstream. I264 itself uses only real rank-one potentials with the fixed scalar profile. No companion proof or referenced history file was read.

## External classical endpoint

Hundertmark–Laptev–Weidl, *New bounds on the Lieb–Thirring constants*, [author-hosted primary PDF](https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf), Theorem 3.1.

Fresh full-PDF retrieval returned 1,192,425 bytes with SHA256 `1e8aac1f8d388ae8e53dfeffd04736a0e00da6b26db6b618023a25d1ffb7f2c1`, matching the finalized I260 authentication. Only pages 3–6 were fully visually read and retained. They were individually copied from I260's authenticated fully read primary renderings after reading and hash verification:

- `hlw-page-03.png`: `a86aeaaf491a9340ef7c53aff3718079f251b984a6eee6dbd7c8210ddb68a042`.
- `hlw-page-04.png`: `0631c2d3f23e2258810177e1cf6c0fce80fe3bc12bbabe4bd387270b7cfbe2d2`.
- `hlw-page-05.png`: `d830c29d19482e181a7e24e62b24707377e040e8883c860db6680785c8a6298b`.
- `hlw-page-06.png`: `b808e2c3ae689ad1902b3fb2d2f8e568ca9519e5e5b4913ee023038e8464cb19`.

Page 3 establishes the form conventions. Theorem 3.1 requires nonpositive operator-valued V, trace class almost everywhere, with integrable tr V_-. It bounds the full negative square-root moment by (1/2) integral tr V_-. Pages 4–6 include Definition 3.2, Lemma 3.3 and its proof, Lemma 3.4 and its proof, and the complete presented theorem proof in Section 3.3. The argument uses unitary-averaging majorization and the Cauchy convolution semigroup to control the scaled Birman–Schwinger kernels. The opening Section 3.4 lines were read but are not used.

For I264 the sign-correct application is V=-B_w w ff^T on G=C^(m-1). It is measurable, bounded, pointwise trace class and nonpositive, with integral tr V_-=B_w integral w|f|²<infinity. The factor 1/2 is independent of channel dimension. No compact-support hypothesis is required. This is a credited external theorem, not a newly proved I264 result. No other section of HLW is claimed read, and the full unread PDF was not written.

## Literature boundaries

The finalized I260 record was permitted background and provided primary excerpt locations. I265 independently verified identities and read the actual statements and page excerpts; I260's PASS is not a premise for the new weighted perturbation or double-interpolation estimates. No I261 or live sibling record was read.

Scalar stability literature, including Carlen–Frank–Lieb mentioned in I264's source record, was not re-read or used as a correctness dependency. No source search for novelty was assigned, and no conclusion about matrix/vector stability overlap follows from this record. The only retained primary artifacts are the two fully read introductions and four fully read page excerpts above.
