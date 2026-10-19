# r114 detached handoff

No target frozen; no nominee. No count, gate, substantiality or independent-review assignment.

Read [report](packet/public/report.md), [reading ledger](packet/public/reading.md), and the four screen notes linked there. The packet's private copies retain original rights.

Final manifest SHA256: `2d6b4b7bfea913434b58df4a54511bac4e9d8b0a87d69f9bb81cee2a0d49ca00`

Report SHA256: `b8d14c716f4677d87a2d5a6bea655d0fb0abd22445a95b37e81bc9974956073b`

Read-only verifier SHA256: `2a7fd5fe85b7e6072380959e7d90f200bee375160ae44712d234c403f455cd23`

Copied-controls script SHA256: `36ca72c19c91d130cc955aa7639d2450f07e57ed730216b2f5271963600b6f36`

These hashes are outside the packet. Supply the final manifest hash from this handoff or the external final message, not from packet content. Trust the verifier code separately.

```bash
python -B packet/public/verify.py packet --expected-manifest-sha256 2d6b4b7bfea913434b58df4a54511bac4e9d8b0a87d69f9bb81cee2a0d49ca00
python -B packet/public/run_controls.py packet --expected-manifest-sha256 2d6b4b7bfea913434b58df4a54511bac4e9d8b0a87d69f9bb81cee2a0d49ca00 --work-directory controls
```

The commands assume the r114 directory as working directory. The control transcript is `controls/final-controls.json`; verification before and after controls is retained alongside it. All controls operate on copies at this exact FINAL anchor. Integrity tests are not mathematical gates. No candidate is forwarded for review/formal/manuscript work.
