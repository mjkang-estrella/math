# Detached verification

Run the trusted verifier with the FINAL SHA256 and report SHA256 received outside this packet. Do not derive those expected values from the packet you are trying to authenticate.

```bash
python3 -B frontier/campaigns/2026-10-14/fresh-analytic-discovery-r120/packet/public/verify.py \
  --root frontier/campaigns/2026-10-14/fresh-analytic-discovery-r120 \
  --tree sources/preprints-tree.json \
  --finalhash "$R120_DETACHED_FINAL_SHA256" \
  --reporthash "$R120_DETACHED_REPORT_SHA256"
```

The verifier rejects missing or mismatched detached anchors, inventory changes, modes, links, canonical-source mismatches, primary/history changes and a wrong complete tree. It reads files only and installs a write/network/subprocess audit guard. FINAL and MANIFEST are outside `packet/`. The manifest includes all packet directories, including empty directories, and all regular files. Work scripts outside the packet are acquisition/discovery aids, not mathematical evidence or trusted integrity inputs.

`integrity_controls.py` is a separate mutation runner. It only creates disposable copies under the owned `controls/` directory and invokes the original verifier on them. Its receipt records acceptance of the valid copy and rejection of altered copies, including a coherently resealed report/manifest/FINAL using the original detached anchor. It snapshots the original owned root excluding the control-output directory before and after and requires equality. The final receipt and its SHA256 are outside packet, since controls run against the final sealed packet. No finite mathematical tests or mathematical gates are implemented.
