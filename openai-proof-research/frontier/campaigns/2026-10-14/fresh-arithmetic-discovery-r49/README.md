# r49 sealed research checkpoint

Status: T127N49 full target unresolved; no nominee. See scope-status.md, working127.md, checkpoint.md and reading-limits.md. Earlier023/252 technical screens are in screen023-252.md. No accepted-count change is requested.

Run `python3 verify.py EXTERNAL_MANIFEST_SHA256` using the separately reported anchor. The verifier never regenerates a seal; it authenticates exact file/directory inventory, source blobs and primary identities, rejecting symlink ancestors, special entries and hardlinks. Run `python3 check.py` for finite support only. Neither command proves the full target or certifies novelty.

All upstream bodies and history copies remain under ignored private/. Source truth is stipulated at the pinned commit. No staging, commits or uploads were performed.
