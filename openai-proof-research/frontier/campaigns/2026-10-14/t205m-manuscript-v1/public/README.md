# The sharp minimum multiplicity in a staircase tensor square

Myeongjin Kang, no affiliation. Original exposition: CC BY 4.0. Original code: MIT.

The article proves the full statement for every m ≥ 2 and every partition of m(m+1)/2 other than row and column, conditional on the explicitly specified pinned source theorems. The lower bound is m−1 and is sharp at (N−1,1). It claims a new-to-project uniform estimate, not demonstrated new-to-literature priority.

`article.tex` is the complete exposition. The sibling `output/pdf/article.pdf` is the rendered manuscript. This public directory contains no third-party source bodies. Bibliographic citations identify those separately.

## Build

From this directory, with Tectonic 0.17.0 and its ordinary LaTeX bundle already cached:

```sh
python3 -B build.py --tectonic /path/to/tectonic --output /path/to/NEW-BUILD
```

The output directory must be new and outside this directory. The builder fixes `SOURCE_DATE_EPOCH=1792281600` and `TZ=UTC`, uses `--only-cached --untrusted`, and retains logs, intermediates and a source/PDF hash receipt. A missing TeX dependency requires a separate ordinary Tectonic cache bootstrap; the reproducibility run itself does not fetch packages. The source date is a deterministic build epoch, not a claim about publication time.

## Exact finite proof supplement

```sh
python3 -B code/verify-finite-proof.py
python3 -B code/finite-crosscheck.py
```

Both use the Python standard library only. The first recomputes the exact small squares for m=2,3,4, the cyclic recursion through m=6, and every nonexceptional boundary label at m=7,8, comparing all results with the supplied certificate. Its final critical-family branch invokes the symbolic LR identity proved in the article for m≥5; it does not numerically establish that identity. The second independently compares grid-cell and beta-set border-strip character computations through degree ten. These finite computations do not replace the uniform proofs.

`finite-proof-certificate.json` SHA256:
`5ffb18808a16add627497b29c82ee389187ad8f4d6df0f6fa52cc6ab49d99263`.

The separate Lean packet is not required to build this article. Its coverage is generic finite-poset rank interpolation, unique-rank ordered cuts and a two-ideal reduction only. The geometric no-cut proof, representation theory, configuration formula, finite bases and full theorem remain unformalized.

`LICENSES.md` gives the licenses. The containing manuscript packet holds private provenance and QA records; those are not part of this public source directory.
