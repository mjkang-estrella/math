# r76 research evidence

Read `research.md` and `reading-limits.md`. This is a pre-freeze, non-nomination archive, not a manuscript or a release candidate. The parent owns all independent gates and campaign counts.

`public/` contains original prose/code and provenance metadata. Original prose: CC BY 4.0. Original code: MIT. `private/` contains pinned upstream and third-party reading bodies under their original rights, plus private history excerpts. These are not relicensed or prepared for publication.

Run the read-only checker with the detached hash from the outer HANDOFF.md:

    python -B packet/public/verify.py --packet packet --expected-manifest-sha256 DETACHED_FINAL_HASH

The expected hash is mandatory and must come from outside `packet/`. The checker validates exact files/directories, regular-file status, hashes, selected canonical Git blob identities, and primary PDF/text receipts. It does not authenticate the Python interpreter, prove source truth, certify reading, or make mathematical/contribution decisions. The full 13,223-entry tree was checked locally; the packet retains its digest and exact selected entries rather than a massive context snapshot. A copied packet can be checked without live workspace files.
