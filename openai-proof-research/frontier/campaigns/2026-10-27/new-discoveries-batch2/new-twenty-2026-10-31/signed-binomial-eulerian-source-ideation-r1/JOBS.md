# Local jobs and resource receipts

All local processes completed and were reaped through exec_command or write_stdin. No background process remains from this lane. No mathematical computation, enumeration, Lean, solver or child job ran. Tool transcript is the primary command/output log.

Initial short bootstrap jobs: pwd/rg listing (output truncated), ancestor AGENTS/TASK reads, lane listings, frozen-manifest display, complete ATTEMPTS read. Explicit CPU/wall/AS wrappers and CPU affinity were not installed for those initial reads. This bootstrap gap is disclosed. The broad first file listing was too noisy and was replaced by precise reads. Later short source/metadata reads without explicit wrappers also inherit this limitation. No retroactive cap claim.

Frozen-before job: CPU120, wall140, AS6GiB, taskset to one allowed CPU. Returned173/173 matching. Chunk81765f. Administrative hashing only.

Source download job: CPU120, wall140, AS6GiB, affinity<=2 CPUs; urllib timeout22 per source, bounded reads5MB, no retry. Session6861 (initial001b40, completedc78ce5) fully reaped. Four source bodies returned200; hashes and UTC in source-receipts.json. Full duration under140 seconds.

PDF text extraction: CPU120, wall140, AS6GiB; sequential pdftotext, no retained process. Chunk4efe55. Output is source text, not mathematical computation.

Source/history/denial review jobs after caps introduced: CPU120, wall140, AS6GiB; small sequential read/parse operations. One metadata job exited1 after comparing a None HTTP status to an integer (d4f835); corrected read used (status or200), exited0 (05eda4). A predecessor-file rg reported absent r297 ATTEMPTS (1928d5); no mathematical conclusion from that failure, no denied network route involved.

Registry head refresh: CPU120, wall140, AS6GiB, affinity<=2, two network workers, timeout15, bounded6MB reads. Session2701 (23599e, completed223ac8), reaped. Three200 receipts in registry-current-receipts.json. Updated pinned Omega README/commit job same bounds, sequential two requests, chunk01b55e, reaped. No APIs or git CLI.

Report/inventory/final preservation jobs: CPU120, wall140, AS6GiB and affinity<=2. These create only administrative/ordinary-proof prose and JSON within assigned lane. apply_patch wrote REVIEW.md within lane only.

Managed web search calls were bounded query batches (3 queries each); platform CPU/AS caps are unknown. Searches are source discovery, not mathematical numeric search. No denied publisher route retried, no alternate publisher API, TLS/auth change, contact, browser or account operation.
