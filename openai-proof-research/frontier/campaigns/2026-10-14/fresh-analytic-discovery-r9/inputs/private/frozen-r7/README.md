# Research handoff r7

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.

Read `candidate.md` for the full proposed theorem and proof; `original-scope.md`
records the fixed quantifiers. The proposed conclusion is the sharp Fréchet
relaxation-time law for every q>4, alpha in (0,1/2), with iid all-edge Pareto
resistances and original-degree speed measure. The campaign remains 4/10.
Separate independent proof and contribution review are required.

All private references and context are under `inputs/private/`, with exact
provenance, source labels and reading limits in the contracts/retrieval files.
Do not include those copies in a public release. No release is authorized here.

The root of trust is the **detached SHA256 of seal.json supplied separately
in the handoff**. The local `seal.sha256` is a convenience copy, not a trusted
replacement. To authenticate before running any stored code, run the following
inline Python from this directory, replacing EXTERNAL_SHA256 with that detached
hash. It authenticates the seal, both inventories and every input/output,
including the verifier and checker, before launching the stored verifier.

```bash
python -B - EXTERNAL_SHA256 <<'PY'
import hashlib, json, pathlib, subprocess, sys
p=pathlib.Path.cwd()
expected=sys.argv[1]
b=(p/'seal.json').read_bytes()
assert hashlib.sha256(b).hexdigest()==expected, 'seal mismatch'
s=json.loads(b)
for kind in ('inputs','outputs'):
    r=s[kind]; b=(p/r['path']).read_bytes()
    assert len(b)==r['size'] and hashlib.sha256(b).hexdigest()==r['sha256']
    for f in json.loads(b)['files']:
        q=pathlib.PurePosixPath(f['path'])
        assert not q.is_absolute() and '..' not in q.parts
        b=(p/f['path']).read_bytes()
        assert len(b)==f['size'] and hashlib.sha256(b).hexdigest()==f['sha256']
subprocess.run([sys.executable,'-B','verify.py','--seal-sha256',expected],check=True)
PY
```

The verifier checks exact file membership, source Git blob identities, and
byte-identical replay of `checks-receipt.txt`. It never regenerates a receipt,
inventory or seal and uses no network. It does not prove F. Its source is short
and should be inspected before replay. Failure returns a nonzero status without
repairing or writing any package files. Mutation tests were performed before the
final freeze, in disposable copies; `mutation-tests.json` records their scope.

No agent, stage/commit, shared-index edit, upload, submission, manuscript or Lean
work was performed. Parent owns integration and any independent-review decision.
