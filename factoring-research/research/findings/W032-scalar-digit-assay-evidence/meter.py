"""Frozen arithmetic-event convention; not a bit-cost model."""
import json
import math
import time
from collections import Counter


class StopAssay(Exception):
    def __init__(self, reason, detail):
        self.reason = reason
        self.detail = detail
        super().__init__(reason)


class Meter:
    def __init__(self, event_path, deadline, cap):
        self.log = event_path.open("x")
        self.deadline = deadline
        self.cap = cap
        self.events = 0
        self.counts = Counter()
        self.max_operand_bits = 0
        self.max_intermediate_bits = 0
        self.max_result_bits = 0
        self.width_square_sum = 0
        self.scope = "setup"
        self.trial = None
        self.pending = None
        self.by_trial = {}

    def check_time(self):
        if time.monotonic() >= self.deadline:
            raise StopAssay("time_budget", {"pending": self.pending})

    @staticmethod
    def width(values):
        return max((abs(v).bit_length() for v in values), default=0)

    def begin(self, op, operands):
        self.pending = {"op": op, "operands": operands,
                        "scope": self.scope, "trial": self.trial}
        self.check_time()
        if self.events >= self.cap:
            raise StopAssay("event_budget", self.pending)

    def end(self, op, operands, results, intermediates=(), detail=None):
        ob = self.width(operands)
        ib = self.width(intermediates)
        rb = self.width(results)
        self.events += 1
        self.counts[self.scope + ":" + op] += 1
        self.max_operand_bits = max(self.max_operand_bits, ob)
        self.max_intermediate_bits = max(self.max_intermediate_bits, ib)
        self.max_result_bits = max(self.max_result_bits, rb)
        self.width_square_sum += max(ob, ib, rb) ** 2
        if self.trial is not None:
            local = self.by_trial.setdefault(self.trial, {
                "events": 0, "event_counts": Counter(), "max_operand_bits": 0,
                "max_intermediate_bits": 0, "max_result_bits": 0,
                "width_square_sum": 0})
            local["events"] += 1
            local["event_counts"][self.scope + ":" + op] += 1
            local["max_operand_bits"] = max(local["max_operand_bits"], ob)
            local["max_intermediate_bits"] = max(local["max_intermediate_bits"], ib)
            local["max_result_bits"] = max(local["max_result_bits"], rb)
            local["width_square_sum"] += max(ob, ib, rb) ** 2
        row = {"event": self.events, "scope": self.scope, "trial": self.trial,
               "op": op, "operands": operands, "results": results,
               "operand_bits": ob, "intermediate_bits": ib, "result_bits": rb}
        if detail is not None:
            row["detail"] = detail
        self.log.write(json.dumps(row, sort_keys=True) + "\n")
        self.log.flush()
        self.pending = None
        return results

    def mark(self, op, *operands, detail=None):
        self.begin(op, operands)
        self.end(op, operands, (), detail=detail)

    def check(self, name, ok, *operands):
        self.begin("control_check", operands)
        self.end("control_check", operands, (int(bool(ok)),), detail=name)
        if not ok:
            raise StopAssay("mismatch", {"check": name, "operands": operands,
                                          "scope": self.scope, "trial": self.trial})

    def mul(self, x, y):
        self.begin("integer_multiply", (x, y))
        return self.end("integer_multiply", (x, y), (x * y,))[0]

    def add(self, x, y):
        self.begin("integer_add", (x, y))
        return self.end("integer_add", (x, y), (x + y,))[0]

    def sub(self, x, y):
        self.begin("integer_subtract", (x, y))
        return self.end("integer_subtract", (x, y), (x - y,))[0]

    def mod(self, x, modulus):
        self.begin("remainder", (x, modulus))
        return self.end("remainder", (x, modulus), (x % modulus,))[0]

    def divmod(self, x, y):
        self.begin("integer_divmod", (x, y))
        return tuple(self.end("integer_divmod", (x, y), divmod(x, y)))

    def mmul(self, x, y, modulus):
        self.begin("modular_multiply", (x, y, modulus))
        product = x * y
        return self.end("modular_multiply", (x, y, modulus),
                        (product % modulus,), (product,))[0]

    def madd(self, x, y, modulus):
        self.begin("modular_add", (x, y, modulus))
        total = x + y
        return self.end("modular_add", (x, y, modulus),
                        (total % modulus,), (total,))[0]

    def msub(self, x, y, modulus):
        self.begin("modular_subtract", (x, y, modulus))
        total = x - y
        return self.end("modular_subtract", (x, y, modulus),
                        (total % modulus,), (total,))[0]

    def gcd(self, x, y):
        self.begin("gcd", (x, y))
        return self.end("gcd", (x, y), (math.gcd(x, y),))[0]

    def inverse(self, x, modulus):
        self.begin("inverse", (x, modulus))
        try:
            result = pow(x, -1, modulus)
        except ValueError:
            self.end("inverse", (x, modulus), (), detail="not_invertible")
            raise StopAssay("mismatch", {"check": "inverse_exists", "x": x,
                                          "modulus": modulus, "trial": self.trial})
        return self.end("inverse", (x, modulus), (result,))[0]

    def snapshot(self):
        return {"events": self.events, "event_counts": dict(self.counts),
                "max_operand_bits": self.max_operand_bits,
                "max_intermediate_bits": self.max_intermediate_bits,
                "max_result_bits": self.max_result_bits,
                "width_square_sum": self.width_square_sum}
