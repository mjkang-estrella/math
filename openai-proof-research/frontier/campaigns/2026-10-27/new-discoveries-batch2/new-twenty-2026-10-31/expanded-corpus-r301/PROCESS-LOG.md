# Process envelope and completion log

This is a retrospective job ledger tied to the tool transcript, not fabricated sampled telemetry. Exact source-fetch start UTC, elapsed wall seconds, return/status/error and child extraction return code are in each *.receipt.json. Python fetch runner uses two worker threads, CPU affinity to at most two allowed CPUs, RLIMIT_CPU=120 seconds, RLIMIT_AS=6 GiB, URL timeout 8 seconds, read cap 16,000,000 bytes and pdftotext timeout 8 seconds. Outer timeout is 140 seconds. No payload reached the byte cap. Child processes inherited limits and were synchronously reaped. Direct research scripts used Python -I -B and the same prelude/outer timeout. The one rg subprocess had a 45-second timeout and inherited the parent envelope. No numerical/mathematical search job was launched.

Tool transcript job groups, in order:

1. Initial pwd/rg/head navigation and full TASK cat: two uncapped calls, exit 0. DEVIATION: CPU, affinity, AS and wall limits not imposed. Cannot retroactively certify compliance.
2. Ancestor instructions/reservation navigation: timeout140, shell CPU120/AS6GiB, exit0. DEVIATION: taskset -pc only queried affinity and did not restrict it. Sequential simple reads, but the required explicit two-CPU affinity cap was absent. Output partly truncated.
3. Capped Python instruction/context and reservation-before read: exit0; large ledger display truncated. Capped extraction/provenance process: exit0, exactly20 recovered.
4. Capped context/registry-navigation reads: first context read exit1 after missing batch STATUS.md; registry rg exit2 due absent expected filenames. Follow-up bounded Python read of existing campaign STATUS succeeded. No denial or network bypass involved.
5. History scans and source excerpt/metadata scripts: bounded to the stated Python prelude; exit0. Broad history scan did not exclude protected lanes before metadata parsing; strict protected non-read isolation cannot be certified. No intentional protected proof-body investigation, targeted poll or edit.
6. fetch-first.json: session96194 completed/reaped, 18 receipts.
7. fetch-more.json: session46756 completed/reaped, registry pinned-head/commit files and older source versions.
8. fetch-breadth.json: session48052 completed/reaped; primary PDFs and current companion bodies.
9. fetch-abs.json: session55172 completed/reaped; source version/journal metadata and rationality PDF.
10. fetch-routes.json: session41511 completed/reaped; multicrossing source and journal-deposited rationality text.
11. fetch-versions.json: session81827 completed/reaped; 11 older available versions.
12. fetch-index.json: session13946 completed/reaped; both LeanPool candidates files and current public Trureturing conjecture listing.
13. Capped ordinary-attempts/result assembly, inventory assembly and final immutable validation: exit0 on completion. All outputs restricted to this lane. Hash manifest covers all current lane files except itself.

Every planned HTTP fetch has one receipt; 82/82 status200, none truncated at the read cap, no denied request retried. TLS verification remained enabled. GitHub API was not called. Public search-tool discovery calls used the provider's managed execution, without a user-configurable CPU/RSS envelope or raw response-byte accounting; do not assert that these managed calls had locally measured resource caps. Authoritative source evidence is retained via capped direct HTTP receipts.

No children, git, shared ledger/index/author edits, Lean, solver, numerical or mathematical enumeration, publication, contacts, browser/account operations. No launched job remains live at handback. The initial process deviations and historical-scan scope caveat are material and appear in SUMMARY.md.
