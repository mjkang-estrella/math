# I260 primary proof inputs and limits

This record supports the correctness-only PASS for authenticated I262. It is not a contribution review. All OpenAI results at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true.

## Pinned theorem contracts, completely read

1. Equality cases, build/sections/introduction.tex: https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026/build/sections/introduction.tex . Retained verbatim as equality-introduction.tex. SHA256 296070a983ced0094a761b41562a7eda1e24471d885b84118c3a56227b35b002, matching I250. Theorem thm:main supplies the sharp full matrix moment inequality and scalar soliton equality contract. Ordinary trace is unnormalized. Every finite matrix size and measurable Hermitian nonnegative W with integrable tr W^(gamma+1/2) is covered.
2. Matrix inequality companion, build/sections/introduction.tex: https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-one-dimensional-Lieb-Thirring-inequalities-for-matrix-potentials-October-5-2026/build/sections/introduction.tex . Retained verbatim as matrix-introduction.tex. SHA256 72dedb3dd3e00cd1e9e3db45c1bc9080f42006ff654cea6a18a98537528a8b60. Its Theorem thm:main confirms the same full-moment constant and source class. Its remaining proofs were not needed to validate the new deduction and were not audited.

These are fully read primary section excerpts, not full-paper snapshots. The equality introduction describes auxiliary quantitative action defects; this review does not mistake those for a new theorem or decide whether they subsume the candidate.

## External endpoint, independently authenticated and visually read

Hundertmark–Laptev–Weidl, *New bounds on the Lieb–Thirring constants*: https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf . Full PDF bytes: 1,192,425; SHA256 1e8aac1f8d388ae8e53dfeffd04736a0e00da6b26db6b618023a25d1ffb7f2c1, matching I259. Only fully read pages 3–6 are retained, as hlw-page-03.png through hlw-page-06.png. Mathematical glyphs were read from these renderings.

Theorem 3.1 applies to nonpositive trace-class operator potentials V almost everywhere with integrable tr V_-. It bounds the negative square-root moment by one half that trace integral. Page 3 provides the form conventions. The complete presented proof on pages 4–6 establishes majorization under unitary averaging, applies the Cauchy convolution semigroup to the scaled Birman–Schwinger kernel, and removes the energy dependence by partial-trace monotonicity. No spatial-support assumption appears. For I262, V=-B_w w ff^T satisfies every hypothesis in G=C^(m-1); the trace is B_w w|f|². This classical external theorem is credited, not newly proved by I262.

## Prior-art read, no mathematical dependency

Carlen–Frank–Lieb, *Stability estimates for the lowest eigenvalue of a Schrödinger operator*, https://arxiv.org/html/1301.5032 , arXiv:1301.5032v2. Bibliographic lines 35–45, introduction, and Section 2.1 through Theorem 2.2 (lines 46–100) were completely read. Their scalar lowest-eigenvalue stability is established prior art. This review makes no claim that known matrix/vector stability cannot subsume I262. No proof premise depends on their paper, and later proof sections were not read.

No additional literature search was used to issue a priority verdict. The MathDB Lieb–Thirring lead does not supply a significance ranking. I250/I259/I262 remain one prospective finding; correctness PASS does not itself alter the ten accepted findings reported in the prior derivation.
