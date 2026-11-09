# Actual source and read inventory

All 20 exact literal statements and full corpus records are preserved. "Retrieved" below never means that an entire paper or its proof was read. Read depth is selected passages of definitions/statements/proofs as specified in results.json and ORDINARY-ATTEMPTS.md. Most targets remain unqualified.

## Primary bodies

Twenty unversioned arXiv HTML URLs (one per reserved record) returned HTTP200 and substantial bodies. Their embedded arXiv version identifiers, byte counts and SHA256 values are in source-inventory.json and http-receipts.jsonl. Converted plain text is local reading support; raw HTML is authoritative for this retrieval. No browser or account action occurred.

The sustained routes read:
- 2301.01924: prescribed J-cubes, Conjecture5.2, singleton Theorem5.3, game-cover bridge. v1,v2 and latest v3 passages agree. Abs lists v1–v3. The 2024 American Mathematical Monthly journal was located by public search; its complete printed proof/figures were not obtained or reviewed. Thus journal/correction gate remains incomplete.
- 2409.11268: Section1 precise partition/image/multiplicity definitions and examples, Lemma3 rooted-count proof, Theorem4 forward differences, Conjecture18 in v1,v2,v3. Abs lists all three. Latest publisher author-hosted PDF URL returned a 212-byte Incapsula challenge despite HTTP200. It is NOT a PDF and NOT proof access. No retry, challenge execution, TLS workaround, or alternate fetch for that denied object followed. Printed tables/figures are not visually audited. No novelty clearance.
- 2407.00551: tensor operators and selected Section8 proof; Section9 Hermitian structure, irreducible cyclic module, diagonal vector, Q norm identity, Conjecture12.2. Abs lists v1 only. Accessible journal DOI10.1007/s10801-025-01420-8 retains Conjecture12.2. Journal conjecture and adjacent discussion read, not all journal proofs.
- 2001.02346: scaffold Krein definitions and selected vanishing derivation; 2110.15848: retrieved Fourier/scaffold companion, limited passage inspection. Neither fully audited. No claim that the companion proves the general target. Current citing-paper coverage is incomplete.

Other primary passages actually inspected are individually listed in results.json. In particular quantum-strategy diagrams and topological figures are not cleared by plain text. No result is excluded merely for ease. Old versions of the other 17 sources were not exhaustively retrieved/reconciled; source qualification remains incomplete. No abstract-only search result is used to certify a solution.

## Public registries, current and pinned

Public GitHub commit pages returned200:
- openai/math observed first main commit4eaee87548250b2682affda7d05d947c05554bae.
- Vilin97/lean-pool observed first main commit01db1d7049cf9668bda1e9e106875ee1278b43e6.

Fetched current CONTENTS.md, LeanPool.lean import index, and LeanPool/projects.yml. Also fetched these three files pinned to the observed commits; hashes match their respective current fetches. Titles/family phrases were screened; the only displayed LeanPool Norine hit concerned Baker–Norine and is unrelated. Empty phrase matches do not establish absence of a theorem. LeanPool import index AND projects.yml are routing only. No candidate-specific public proof was relied on. No GitHub API requests occurred.

Immutable local OpenAI upstream.json pins fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and the local CONTENTS snapshot was inspected by targeted text processing. Its truth is accepted as instructed. No upstream audit and no source theorem dependency was asserted. No registry observation is represented as global novelty clearance. Commit/publication chronology is insufficient to establish precedence here; no precedence claim is made.

## History

Read only the refreshed allowlist's 261 exact results paths, permitted shared root ledger/STATUS, and applicable root prior-campaign metadata. No recursive campaign directory traversal, no protected crown lane access and no individual historical source tree reads. Source-family phrase hits include unrelated token-graph homology, cube-covering and winding-knot items: these are routing matches, not duplicates of the exact target. See history-scan.json and history-matches.json for bounded excerpts. The task's explicit known exclusions, R301 and R302 corrections remain in force.

## Receipts and resource limits

Every shell invocation used actual taskset affinity and timeout, plus CPU/address-space ulimits from the first command. First invocation dynamically selected two allowed CPUs, wall120s CPU110s AS4GiB; subsequent commands CPUs0,1 wall140s CPU120s AS6GiB. Python scripts used -I -B. No mathematical search program was run.

resource-log.jsonl has actual sampled process affinity, rlimits and ru_maxrss for extraction, fetch batches and conversion, with a final sample. These are samples, NOT comprehensive per-command high-water telemetry. Initial administrative reads and several short follow-up text processes have tool exit receipts but no individual persisted RSS log. One shell-quoting script failed before execution of its intended code; one conversion failed because bs4 was absent, then stdlib HTMLParser was used. No cap breach is evidenced, but full per-process RSS logging was not implemented; this is a compliance limit, not fabricated telemetry.

Managed web-search calls have provider-managed limits; local CPU/AS/affinity cannot be imposed on that tool. No local telemetry is claimed for them. Search outputs2/3 are preserved separately; first managed search is preserved in conversation tool receipt only (not a local full transcript). HTTP fetch receipts record UTC,status,error,bytes,hash and name. HTTP200 does not imply usable source access. No denied endpoint was retried. All yielded shell sessions subsequently returned exit0; no background jobs were launched.
