# T117Q manuscript v3

Myeongjin Kang, no affiliation. Required R1-only author implementation; fresh independent narrow manuscript closure remains required. No acceptance or count decision.

Exactly four double-hyphen options now use TeX -{}- to suppress en-dash ligatures. All other article bytes, scope, mathematics, attribution and formal limits are unchanged from v2. validation/v2-to-v3.patch exposes every source change. GMN Question3 was NEW in v2, not retained from v1; the accurate article text remains unchanged.

Build with a fresh output directory:

    python3 -B build.py --output /var/tmp/NEW-T117Q-V3-BUILD --tectonic /path/to/tectonic

Default Tectonic: /tmp/frontier-typeset/tectonic. SOURCE_DATE_EPOCH=1792281600. Cached dependencies are trusted; the build is not hermetic. No Lean rebuild:31 support and15 control declarations remain scoped support, not a formal proof of the full theorem.

Use the externally supplied final manifest hash:

    python3 -B verify.py --anchor EXTERNAL_SHA256
    python3 -B integrity_controls.py --anchor EXTERNAL_SHA256

Controls use disposable /var/tmp copies. Identity is not a mathematical verdict. The preliminary-seal control receipt is inside; final-seal replay is external to avoid self-reference.

The16-page build is clean. All four options extract as ASCII double hyphens. Page14 was visually inspected at160dpi; the other15page renders are byte-identical to v2. Complete source/text diffs and render identities are in validation/. v2-history and earlier history retain their historical status. Original input copies are unchanged; inputs/t117q-manuscript-review-r2 is the exact authenticated new report package.

Original prose CC BY4.0 and code MIT; see LICENSES.md. Private third-party bodies and renders remain private. This local packet is not a public release selection. No frozen packet, ledger, index, commit or upload was changed.
