The first root verification stopped after both r185 private scripts succeeded:
the wrapper looked for power_checks.json, but the supplied script writes
power-checks.json. FileNotFoundError; guarded exit 1, sampled group RSS
32,079,872 bytes, wall 0.361 seconds. Corrected only the wrapper's output
filename. No candidate bytes were edited and no PASS receipt was emitted.
