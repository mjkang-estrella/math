# Preserved failures and qualification

- `attempt01.log` / guard receipt: broad `import Mathlib` exceeded fixed groupRSS2800MiB; killed. Peak sampled3030200320 bytes. No cap raised; narrowed imports.
- Attempts02–03: missing order-big-operator imports, deprecated real import and unresolved Bool-sum import. Attempts05–07: zero-length word sum simplification and unused-simp-argument errors. Attempt04 passed the earlier core; attempt08 passed the expanded finite core. Original error logs and guard receipts remain.
- `fresh-replay/replay-driver.log`: all mathematical/audit modules compiled, but helper parser failed on wrapped axiom reports. The parser was corrected to accept multiline bracket contents. The complete failed extraction is retained; successful replay is in `fresh-replay-02`.
- Initial native `rg` with a large shell glob hit argument-list length; no scientific inference depended on it.
- No attempt at a full 241-coefficient kernel replay or source-clock/analytic bridge was completed. No time/resource-limit failure proving infeasibility is claimed for those tasks; they remain open research/implementation obligations.
- Inherited exploration failures and access holds remain in frozen candidate/review notes. No denied access route was retried here. No source endpoint PASS or novelty clearance follows from component success.
