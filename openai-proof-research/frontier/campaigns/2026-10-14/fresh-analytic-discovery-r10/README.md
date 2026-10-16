# Analytic discovery r10 — unresolved research

Author: Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.
Third-party inputs stay private with their existing rights.

Read `candidate.md` for the complete frozen problem P, supporting proofs,
unpaid contact/density completion, operation comparison and limits.
`status.json` says UNRESOLVED. No nomination or count change: 4/10.
No mathematical checker, simulation, Lean or manuscript was produced.

The local input tree is frozen. Large historical trees are referenced
read-only through their supplied detached seals, not copied. The current
mutable campaign ledger has one small private snapshot. All downloaded
third-party texts remain under `inputs/private/`.

## Authenticate before executing stored code

Obtain the detached `seal.json` SHA256 from the external terminal handoff.
Do not trust an edited seal merely because its adjacent text agrees.
From this directory, an independent inline Python bootstrap can authenticate
every local payload, including the verifier, before executing it:

```python
import hashlib, json
from pathlib import Path
r = Path.cwd()
external_anchor = "REPLACE_WITH_EXTERNAL_TERMINAL_SEAL"
sha = lambda b: hashlib.sha256(b).hexdigest()
raw = (r / "seal.json").read_bytes()
assert sha(raw) == external_anchor
s = json.loads(raw)
for kind in ("inputs", "outputs"):
    record = s[kind]
    b = (r / record["path"]).read_bytes()
    assert len(b) == record["size"] and sha(b) == record["sha256"]
    for item in json.loads(b)["files"]:
        p = r / item["path"]
        assert not p.is_symlink()
        payload = p.read_bytes()
        assert len(payload) == item["size"] and sha(payload) == item["sha256"]
print("Authenticated local payloads, including verify.py; no stored code run")
```

Then run with Python bytecode disabled:

    python3 -B verify.py --seal-sha256 EXTERNAL_TERMINAL_SEAL

The verifier reads the existing frozen manifests and receipts. It downloads,
rewrites, regenerates and executes none of the research inputs. It checks
the pinned Git blobs, frozen scope, all local bytes, exact file/directory
membership and exact historical package membership. The default repository
root is the existing workspace. `--repo-root /absolute/path` explicitly
selects it for a read-only relocated copy.

Exit 0 means artifact integrity only. Exit 2 means failure. Expected negative
controls use a wrong anchor or `--require-status PROVED`; both read the same
unchanged trees. No fixture regeneration is needed. The terminal handoff
reports actual success/failure controls and preservation; it is not an
independent mathematical proof or contribution review.
