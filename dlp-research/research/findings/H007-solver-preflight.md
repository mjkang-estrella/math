# H007 GRR solver preflight: no instrumented engine yet

Native Sol /root/h007_fullcost_schedules inspected primary implementation sources,
read-only. No package installed, solver executed, code edited, or numerical trial.
Root inspected the actual environment: Python3 only among requested executables;
SymPy, Sage, Singular, Magma and the listed Python algebra modules unavailable.

SymPy supplies improved Buchberger and F5B, NOT F4. Neither inspected algorithm
has a progress/cancellation callback. Algorithm source inspected was master;
arithmetic files were1.14.0. Any implementation must first pin one consistent
release rather than silently combine these versions.
https://raw.githubusercontent.com/sympy/sympy/master/sympy/polys/groebnertools.py
https://raw.githubusercontent.com/sympy/sympy/1.14.0/sympy/polys/rings.py
https://raw.githubusercontent.com/sympy/sympy/1.14.0/sympy/polys/domains/modularinteger.py
https://raw.githubusercontent.com/sympy/sympy/1.14.0/sympy/polys/domains/finitefield.py

A domain-method wrapper misses coefficient operators called directly in term
loops. A coefficient wrapper alone still misses monomial comparisons/divisibility,
pair selection, leading-term scans, copies and polynomial construction. Import,
setup, initial reduction and final reduction are also paid. Inversion/powering
need declared charged schedules, not arbitrary single-event calls.
An honest diagnostic would need narrow source hooks or an independently audited
adapter, shared counter and watchdog. Memory/elapsed time remain separate
implementation metrics; algebraic events are not every machine instruction.
Cap exception or watchdog kill is censored, never proof of emptiness.

Builder checks should establish the norm division identity, shift, Graeffe
even/odd coefficient identity and exact variable/equation counts using coefficient
arithmetic, without an uncharged validation solve. Fp arithmetic is required.
Rational extraction cannot stop at a completed Groebner basis: branch/specialize
principal coefficients, find ground-field roots, charge degenerate branches and
all renewed solves, then verify auxiliary chain/root multiplicities/gcd/orientation.
No hidden multivariate rational-root oracle or free full-field scans.

Proposer suggested a k2 planted fixture and an independent unconditioned target,
under one shared60s/1M-event budget. That is only a correctness/operational
diagnostic, not useful-yield/scaling evidence, and would not test an F4 hypothesis.
Cap fit remains unproved. No matched full-solver comparator has been frozen for it.

Root decision: do NOT build a general polynomial engine or launch that diagnostic
merely because Buchberger is available in a package. A concrete justified solver,
candidate-specific narrow instrumentation, extraction and matched control must
be specified before execution. This is a research-implementation gap, not a
global external blocker or a reason to call the active goal complete.
