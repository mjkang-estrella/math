# Root verifier schema correction

The first root verifier stopped with `KeyError: 'original'` while reading alias metadata. This lane uses `reference_absolute` for aliases, while qualified reports use `original`. The guard returned exit 1, sampled peak group RSS 30298112 bytes, wall time 0.24053615902084857 seconds. No scientific mismatch was reported and no worker files were changed.

The verifier now resolves the two documented fields explicitly, retaining alias status rather than promoting references to originals. Its preparation script reproduces that correction. A complete guarded replay and before/after freeze verification follows; the initial failure is not a PASS.
