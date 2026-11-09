# Correspondence

## 6. Formal statement correspondence and proof architecture

The delivered proof packet is the byte-identical riordan-formal-r2 archive, SHA-256

```text
27175a85484d563031a12665736dbd4277de327cb726e1b6791d07a348c2c063
```

It contains 22 Lean modules: 20 proof modules and two audit-tooling modules. This manuscript lane safely extracts and hashes the archive but does not execute Lean, lake or leanchecker. The original finite endpoint and its proof sources are preserved. The additional infinite endpoint makes the extension argument a formal theorem as well.

| Mathematical object or statement | Lean definition or endpoint and scope |
| --- | --- |
| Polynomial and integer convolution, (2)-(3) | Core: gc, pc, polynomial coefficient lemmas, entry and sourceEntry; exact coefficient bridge |
| All 225 adjacency entries | Row0 through Row14 and Table: ordinary arithmetic proofs and assembled matrix identities |
| Canonical odd copy and independent even set | odd_copy and even_independent; zero-based even indices represent source odd vertices |
| Real nonzero kernel vector with nonzero odd part | Endpoint: xR, kernelR, odd coordinate at index 0; no mod-2 kernel substitution |
| Finite-definition refutation | Riordan.source_conjecture_false: negation of SourceConjecture, a sufficient polynomial/canonical specialization of the source universal assertion |
| Infinite binary series and every-index recurrence | InfiniteFamily: h, hZ, h_binary, h_io, h_zero, h_agrees; h uses ordCompl[2](m+1) |
| Locality and the literal Bell coefficient formula | seriesPow_local, seriesEntry_local, seriesBell_entry and h_bell_witness; truncation is proved harmless |
| Infinite-family refutation | Riordan.source_conjecture_false_infinite_family: negation of SourceConjectureInfiniteFamily, quantifying integer coefficient sequences |

The finite predicate specializes the source assertion to natural-coefficient polynomials and the stronger canonical odd-copy property. This strengthens its hypotheses, so a counterexample in this subclass refutes the broader finite claim. It does not purport to encode every possible finite isomorphism. The infinite predicate quantifies unrestricted integer coefficient functions a, assumes a_0 mod 2 = 1 and a_(2j+1) mod 2 = a_j mod 2 for every j, then quantifies n ≥ 2, singularity and every real kernel vector. Singularity is separately defined by the existence of a nonzero real kernel vector.

An integer formal series is represented by its unrestricted coefficient function; powers are finite convolution. EndpointStrong proves agreement with the literal polynomial Bell coefficient formula through seriesTrunc and seriesBell. It transports the frozen matrix certificate using h_witness, proves the two finite io conditions for h, and contradicts the universal conclusion with xR at index 0. No assumed equivalence between arbitrary finite isomorphisms and the infinite identity bridges the two endpoints.

The formal refutations certify the coefficient semantics, the relevant io properties and the kernel obstruction. Nullity 1, the contextual block ranks, the finite n = 7 remark, exhaustive search minimality and literature conclusions are ordinary mathematics or external audit evidence, not extra claimed Lean endpoints. This scope separation is essential to interpreting the packet.


