# Analytic r130 handoff: PREFREEZE, no nominee

Runner: Factory Droid / claude-opus-5-5 / high. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Tree
eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b (13223 entries). This handoff assigns no gate,
verdict or count; those belong to the parent.

- Status: no scope was frozen and nothing is nominated.
- Family 072 (Brennan and its strict companion): the general-exponent run of the printed mechanism (S1)
  indicates B(t) < t^2/4 on (-2,0). It is a parameter substitution with one new factorisation,
  (4 beta - s^2)(beta + s + 1), so it is technical. At positive exponents the mechanism fails at the escape area
  tail and the real-axis covering step.
- Preemption: arXiv:2610.23853v1 (Binder, Ivrii, Prause, Smirnov, 16 Oct 2026) states B_b(t) <= t^2/4 on
  [-2,2], strict on ]-2,2[ \ {0}, and B(t) < t^2/4 on ]-2, 6-4sqrt2[ \ {0}. It gives a full deterministic proof of
  the non-strict inequality and defers strictness. No project record of this note was found. It bears on any
  future 072 or Kraetzer work.
- Open gap: a full proof of strict B_b(t) < t^2/4 for t in (0,2) needs a quantitative maxima-over-saddles excess
  at positive exponents. I have no argument for it, and its novelty is limited because the result is announced.
- Family 213: the site-percolation extension needs a full rerun of the bond proof, so it was dropped.
- Public: packet/public/report.md, screens.md, reading-limits.md, search-receipts.json, verify.py and controls.py
  (MIT). Private: authenticated upstream bodies with register, copied context and history with registers, the
  literature receipt, notes and tools.
- Integrity: run `python3 -B packet/public/verify.py --root ROOT --final-sha256 <FINAL> --report-sha256 <REPORT>`
  with the detached anchors supplied by the runner. The copied controls are recorded in CONTROL-RESULTS.json.
  These are byte and inventory checks only.
