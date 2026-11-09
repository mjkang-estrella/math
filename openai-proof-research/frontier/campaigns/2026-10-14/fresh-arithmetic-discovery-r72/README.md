# fresh-arithmetic-discovery-r72 — T179A

Outcome: **one full candidate theorem with a complete author proof (T179A); no
independent gate has run; no count claim.** The author expects that a separate
contribution review may classify it TECHNICAL (see `primary-comparison.md`).
Priority is not cleared: four relevant primary bodies were not accessible.

**T179A.** (a) For n with 4 ∤ n, a circulant complex Hadamard matrix of order n
with entries in {±1, ±i} exists iff n ∈ {1, 2}. (b) For n with 9 ∤ n, one with
entries in {1, ω, ω²} exists iff n ∈ {1, 3}. Equivalently, perfect quaternary
sequences of length n ≡ 2 (mod 4), n > 2, and perfect cube-root sequences of
length n with v_3(n) = 1, n > 3, do not exist.

Source: family 179 (*The circulant Hadamard conjecture*), pinned at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, stipulated true. The proof reruns its
alternating-product torsion proposition for C_m and coefficient rings ℤ[i],
ℤ[ω], and replaces its binary identity by alphabet-specific normalizations and
first-order identities isolating the all-ones element.

Files:

- `scope-freeze.md` (+ `scope-freeze.sha256`): frozen statement, source
  dependency, honest chronology, contribution risk stated before proof writing.
- `proof.md`: complete proof, hypotheses map, paid/unpaid operations.
- `barriers.md`: why the method stops (orders 4m, 9m; other alphabets;
  Lander-type groups), two exact algebraic barrier examples, a proved inertia
  lemma (method support only).
- `primary-comparison.md`: literature actually read, unread bodies, new orders
  covered, operation-level comparison, author's expectation.
- `screening.md`: families screened and why; T242Z excluded as an existing
  recovery-r4 chain.
- `reading-limits.md`: exact reading extents and failed retrievals.
- `exact-check-results.json` from `tools/check_identities.py`: exact finite checks
  of every coefficientwise identity and the barrier examples (integrity only).
- `controls.json` from `tools/search_small.py`: exhaustive searches for orders
  ≤ 10 (fourth roots) and ≤ 12, 15 (cube roots); consistency only.
- `source-receipts.json`, `primary-identities.json`, `status.json`.
- `tools/`: pinned fetcher, checks, `make_manifest.py`, read-only `verify.py`,
  copied-mutation `controls.py`.
- `MANIFEST.json`, `FINAL.json`: sealed packet. Verify with
  `python3 -I -B tools/verify.py --root . --finalhash <DETACHED_FINAL_SHA256>`
  using the hash from the handoff message, not from any file here.
- `private/` (git-ignored): pinned upstream copies, screening TeX, third-party
  primary copies. Not original work; not for redistribution.

Original prose and code: Myeongjin Kang; prose CC BY 4.0, code MIT.
