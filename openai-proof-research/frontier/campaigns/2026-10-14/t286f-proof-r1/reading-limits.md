# T286F proof r1: exact reading, search and validation limits

## Read in full
- Repository rules: AGENTS.md, sources/upstream.json (pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb), VALIDATION.md, NEW-TEN-2026-10-14.md lines 1–40 (status, acceptance rules, model allocation) plus grep of the T286F dispatch entry (lines 1412–1416).
- Parent: t286f-parent/proof-r1-dispatch.txt, review-dispatch-r1.json, sealed-preflight.json (contribution-r1-dispatch.txt was not opened beyond its hash).
- Author packet (authenticated first): candidate286f.md, scope286f.md, scope286f-freeze.json, checkpoint.md, source-and-credit286f.md, reading-limits.md, kernel-proof286f.md, formal-interfaces286f.md, integrity.md, verify.py, control-tests.py, .gitignore, context-identities.json.
- Pinned sources (authenticated copies inside the packet, read in full): Arithmeticity companion `build/sections/00-introduction.tex`; arithmetic-category companion `build/sections/01-introduction.tex`, `02-models.tex`, `03-calculus.tex`.

## Read in part
- EGNO author's final text extraction (packet private/primary/EGNO.txt) lines 8925–9175: Proposition 7.11.1 through the start of the proof of Proposition 7.12.18, including Remark 7.12.5, Lemma 7.12.6, Theorem 7.12.11, Definition 7.12.17 and the following note. Grep hits only for Definition 9.7.1 and Proposition 9.7.9 (not reread).
- Izumi 2018 text extraction lines 35–74 (printed p474 introduction). Later sections unread; used only to judge the citation (optional O4).

## Not read / not used
- Geometric proof of arithmetic exhaustion (sections 01–11 of the Arithmeticity companion) and 04-endpoints/05-examples of the category companion: stipulated or irrelevant; not audited.
- Vaes 2008, Donvil–Vaes, BKLR, Morales et al., Gödicke bodies: not read in this review. The proof verdict does not rely on them; BKLR's type-III statements were deliberately not substituted for the II_1 bridge, which was checked directly.
- Family 280/308 material, screens, work286.md, work308.md, receipts JSONs: identity-checked only.
- No parallel reviewer drafts, no contribution-review material, and no additional third-party bodies were consulted. No web searches were performed.

## Validation actually run
- External anchor and named-file SHA256 checks against the dispatch values, before trusting any inventory.
- Author verify.py on an authenticated disposable copy in /var/tmp/t286f-proof-r1-R8NYRZ/packet: PASS_EXACT_INVENTORY with the correct anchor; FAIL "external manifest anchor mismatch" with a zero anchor.
- Independent canonical source check (independent-source-check.py) against the repository's own sources/preprints-tree.json (SHA256 eeecc1da…9b, 13223 entries, truncated=false): all 64 selected non-PDF blobs match git-blob SHA1 and receipt SHA256; selected set equals the complete non-PDF family set; 81 family entries; four context copies match repository originals.
- Author control-tests.py run only inside the /var/tmp copy: PASS_13_INVENTORY_CONTROLS, every rejection reason-checked by the script and listed in author-packet-checks.json. Afterwards the copy reverified and `diff -r` against the canonical packet showed it byte-identical; no scratch remained; the canonical manifest SHA256 is unchanged.
- This review directory has its own externally anchored verifier (verify.py) and copied reason-checked controls (control-tests.py), whose scratch lives in the system temp directory, never inside this directory or the author packet.

These integrity checks are byte checks only. They are not mathematical evidence.
