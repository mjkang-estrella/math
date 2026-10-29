# Acceptance integration notes

The final source-only replay passed without retries or mathematical edits.
An initial acceptance-script assertion counted 78 `*.log` paths because each
of the 39 Lean logs has a driver log. Accounting had not yet been changed.
The assertion was narrowed to the actual 39 `*.lean.log` files; every one is
byte-identical to the independent final review's fresh output. The corrected
acceptance script then completed. No proof or axiom audit was relaxed.

Preparation and acceptance scripts are one-shot transitions with assertions;
re-running acceptance after it is recorded intentionally fails the old-count
guard. Reproduction of the theorem uses the archived scripts/replay.py instead.
