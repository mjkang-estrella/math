# Read-only authentication

Obtain the detached FINAL.json SHA256 from the handoff, outside this packet. Run:

```sh
python -B packet/public/verify.py --root . --finalhash DETACHED_FINAL_SHA256
```

The verifier authenticates FINAL.json before trusting its MANIFEST.json and REPORT.md bindings. It checks exact packet membership, bytes, selected canonical Git blobs, pinned raw URLs and primary PDF/text identities. It writes nothing. It does not authenticate mathematical truth, contribution, priority or a campaign gate.

The exact packet is under packet/. REPORT.md, MANIFEST.json and FINAL.json are outsidepacket. Work scripts and control logs are outside the sealed packet; they are not mathematical evidence silently supplied to a proof. Selected acquisition/search receipts are inside private/.

The optional copied-control runner writes temporary copies and its results only under controls/ of the supplied root:

```sh
python -B packet/public/run_copied_controls.py --root . --finalhash DETACHED_FINAL_SHA256
```

It uses the original sealed verifier against copied packets. Its clean copy should be accepted, while twelve deliberate integrity failures should be rejected. It checks that original packet/anchor bytes remain unchanged. This is an integrity experiment, never a mathematical gate. The reported control-log hash is an additional detached receipt, not part of the circularly sealed packet.
