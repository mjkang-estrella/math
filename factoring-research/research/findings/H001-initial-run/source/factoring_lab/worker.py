"""One trusted local candidate in a killable subprocess; not a security sandbox."""
import json
import sys
import time
import tracemalloc
from random import Random

from .algorithms import ALGORITHMS
from .core import BudgetExceeded, Meter, valid_factor


def evaluate(request: dict) -> dict:
    meter = Meter(request["max_events"], request["max_operand_bits"])
    d, detail = None, None
    tracemalloc.start()
    start = time.perf_counter()
    try:
        d = ALGORITHMS[request["algorithm"]](request["n"], Random(request["seed"]), meter)
        status = "no_factor" if d is None else "success" if valid_factor(request["n"], d) else "invalid"
    except BudgetExceeded as exc:
        status, detail = "event_budget", str(exc)
    except Exception as exc:
        status, detail = "error", f"{type(exc).__name__}: {exc}"
    elapsed = time.perf_counter() - start
    _, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    return {"status": status, "factor": d, "detail": detail,
            "solver_seconds": elapsed, "python_peak_bytes": peak, **meter.snapshot()}


if __name__ == "__main__":
    print(json.dumps(evaluate(json.load(sys.stdin)), sort_keys=True))

