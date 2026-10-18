# T298P scoped Lean support

Author implementation only; full theorem remains unformalized and unaccepted. Myeongjin Kang, no affiliation. Original prose CC BY 4.0; code MIT (LICENSE-CODE.txt).

Run the identity check with the separately supplied manifest SHA256:

```
python -B verify.py --anchor EXTERNAL_SHA256 --repo /path/to/openai-proof-research
```

For a fresh copied build, copy the payload to a fresh directory and run:

```
python -B rebuild.py --output /var/tmp/NEW_OUTPUT --lean /path/to/lean-4.34.1-linux/bin/lean --cache /path/to/formal/.lake/packages
```

The output must not exist and must lie outside the package. Explicit `--lean` and `--cache` make the copy portable; defaults are local conveniences only. No network or package installation is used. The runner checks Lean version/commit and dependency Git revisions/clean tracked sources, then builds fresh support/control oleans and prints every theorem type and axiom dependency. See coverage.md for premises and exclusions.

The dependency oleans are a trusted pre-existing cache; they are not rebuilt from source. Neither Git cleanliness nor compiler version verifies all cached compiled artifacts. Compiler binary SHA256 and revisions are recorded. This is scoped reproducibility within that trust boundary, not a fully bootstrapped proof audit.
