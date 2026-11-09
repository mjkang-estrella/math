# Replay the partial r4b source packet

Extract `nut-r4b-source.zip` into a **new empty directory** inside the assigned
lane. The zip contains source only and does not include inherited binary inputs
or build products. Set the following variables and run from the extracted tree:

```sh
export LEAN_BIN=/path/to/lean-4.34.1-linux/bin/lean
export LEAN_PACKAGES=/path/to/pinned/mathlib/.lake/packages
python3 -I replay_r4.py
```

Lean is pinned to 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`; mathlib is pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Package paths are read-only.
The driver sanitizes the child environment and confines HOME and TMPDIR to the
extraction directory. It refuses any existing olean under that directory and
refuses to overwrite existing replay logs. Do not run it at the lane root,
which contains read-only copies of inherited binary inputs.

Every one of the 60 Lean modules is compiled sequentially with `-j1` and
`-DwarningAsError=true`, followed by a separate leanchecker call. This includes
all 56 inherited source files and four new modules. The new audit imports all
local modules and prints every local declaration's module, full type, opaque
body, unsafe/partial/axiom flags and transitive axioms. Only propext,
Classical.choice and Quot.sound are allowed. Six false Lean controls must fail.
An existing-olean refusal is checked separately and recorded in the lane logs.

The per-call watchdog enforces two CPUs, 6 GiB sampled private memory, 120 CPU
seconds, 140 wall seconds and MALLOC_ARENA_MAX=2. Full logs and JSON receipts
are retained, including failed development trials under unique names.

The recorded fresh replay was extracted from `replay-candidate-source.zip`.
The final `nut-r4b-source.zip` adds documentation and manifests; the formal theorem
sources are checked for byte identity with the tested extraction.
A passing replay means **partial packet only**, never the desired endpoint.

Validation correction: the initial new permutation-lookup negative control lacked
an explicit finite dimension and also produced elaboration errors. Its complete
log is retained. The corrected control specifies `(n := 2)` and was rerun under
the same watchdog; it is rejected solely with the intended unsolved `False` goal.
The portable driver includes that one-line correction. All formal theorem sources
and compilation commands are byte-identical to the strict fresh extraction; the
corrected control was validated separately without repeating unchanged builds.
The main replay has 126 receipts and the supplementary corrected control has one.
