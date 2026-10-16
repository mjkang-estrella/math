# r8 handoff

Read candidate.md and original-scope.md. Status is UNRESOLVED; campaign
count remains 4/10. All proved material is technical support. No independent
mathematical or contribution PASS is asserted.

Original author: Myeongjin Kang; no affiliation. Prose CC BY 4.0; original
code MIT; see RIGHTS.md. Private third-party sources retain upstream rights.

The input and output manifests freeze every retained file by SHA256 and
byte size. seal.json binds both manifests. seal.sha256 is a detached anchor
outside those inventories. Obtain the trusted seal hash from the parent
handoff/final message; an editable local anchor is not by itself trust.
Hashes are integrity checks, not signatures or proof certificates.

Authenticate the verifier before executing it. From this directory, replace
TRUSTED_SEAL_SHA256 with the external handoff value and run:

```sh
python -B - TRUSTED_SEAL_SHA256 <<'PY'
import hashlib, json, pathlib, subprocess, sys
r=pathlib.Path.cwd()
anchor=sys.argv[1]
digest=lambda b:hashlib.sha256(b).hexdigest()
seal=(r/'seal.json').read_bytes()
assert digest(seal)==anchor
s=json.loads(seal)
manifest=(r/'outputs-manifest.json').read_bytes()
entry=s['manifests']['outputs-manifest.json']
assert len(manifest)==entry['size'] and digest(manifest)==entry['sha256']
v=next(e for e in json.loads(manifest)['files'] if e['path']=='verify.py')
b=(r/'verify.py').read_bytes()
assert len(b)==v['size'] and digest(b)==v['sha256']
raise SystemExit(subprocess.call([sys.executable,'-B',str(r/'verify.py'),anchor]))
PY
```

The verifier authenticates all files and ten pinned Git blobs before
executing either checker. It compares immutable stdout receipts, never
regenerates them, and compares its complete package snapshot in a finally
path on both success and failure. Both authenticated checkers are read-only
on all branches; bytecode generation is disabled. No network or sibling
tree is needed. It performs no repair, freezing or receipt generation.

After authenticating verify.py, two deliberate failure tests are available:

- Wrong external SHA256: verification must reject before executing code.
- `python -B verify.py TRUSTED_SEAL_SHA256 --exercise-checker-failure`:
  authentication succeeds and the first authenticated checker intentionally
  exits unsuccessfully before its calculation. Verification must reject
  with `frozen_tree_unchanged: true`.

For either test, preserve the original trusted anchor and files. The tests
need no corruption or disposable-copy mutation. The parent should also
take its own before/after whole-tree hashes, independent of the verifier.

checks.py computes actual coloring coefficients through n=6 with exact
rationals and verifies the diagnostic skew matrices, characters and
polynomials. mutation_probe.py is explicitly bounded exploration. Neither
program proves U or implements the source's full theta algorithm.
