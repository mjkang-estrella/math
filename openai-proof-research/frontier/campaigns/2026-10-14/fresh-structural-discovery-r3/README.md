# Structural discovery r3

Read [candidate.md](candidate.md) for the exact all-prime, all-group theorem,
proof, source boundary, antecedents and contribution objection.

The proposed new theorem gives universal subgroup-count residues for every
finite iterated extension of Z_p, at precision p^(h+1), uniformly over all
open subgroups and with the stated closed-subgroup extension. A related
arithmetic characterization uses two explicitly stipulated pinned lemmas.

No acceptance or independent review is claimed. No Lean certificate exists.
The parent should commission separate full proof and contribution reviews
only if this package is a viable substantial candidate. In particular the
contribution review must confront GRV's torsor argument and Kisilevsky's
orbit divisibility, not merely check that the theorem was not in the catalogue.

Authenticate the detached SHA256 of `seal.json` from the handoff, then run:

```sh
python3 -B verify.py
```

The verifier authenticates the complete immutable input/output inventories
and the stored receipt before executing the checker. It performs no writes,
downloads, resealing or receipt repair. Python 3.10+ and its standard library
are sufficient. The PDF extraction software used during research is not
needed for verification. If testing a writing workflow or a mutation, use
only a disposable copy; do not change the frozen package.

`inputs/` contains private/local third-party reading copies and context
snapshots. It is excluded from the releasable-original inventory. Those
copies retain their own rights. All other authored prose is CC BY 4.0 and
original code is MIT; metadata identifying third-party material grants no
new rights to that material. Author: Myeongjin Kang, no affiliation.

This is a research handoff, not a publication-ready paper or archive.
No upload, submission, external message, commit, shared edit, or count change
has been made.
